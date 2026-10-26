/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Bank
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Frame.Retained
import all QuantumAlg.Core.Execution.Classical.Retained.Cells

/-!
# Persistent P-256 table cells before the owned-layout view

The ten table cells are allocated by
`Circuit.retain` and remain live. The constructor for `Outer.Frame` consumes
their actual typed references, rather than lexical workspace references.
The view's five fresh slice keys are derived above the maximum live key of
the fully retained context, then substituted for the original bank key.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.ClassicalRoutines.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The actual table allocation extends the prepared bank and results. -/
def tableContext : RuntimeCtx .quantum :=
  RetainedCells.context (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256)

/-- The table cells are ten charged retained instructions in sequence. -/
def prepareWithTables {services : ClassicalOracleModel} :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      base (tableContext base noQuantum) :=
  (prepare (services := services) base noQuantum).seq
    (RetainedCells.allocate
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (resultContext base noQuantum) (WindowTables.Outer.sharedShapes 256))

/-- Ten typed persistent references form the existing shared table frame. -/
def tableFrame : WindowTables.Outer.Frame (tableContext base noQuantum) 256 :=
  WindowTables.Outer.Frame.ofRetainedCells
    (RetainedCells.references (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256))
    (RetainedCells.references_keys_nodup (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256))

/-- Retention transports both original measurement streams without renaming. -/
def resultsAfterTables : Fourier.Results (tableContext base noQuantum) where
  cells := fun position =>
    (RetainedCells.transport (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256)).liftWrite
      ((preparedResults base noQuantum).cells position)
  distinct := by
    intro first second same
    apply (preparedResults base noQuantum).distinct
    simpa only [ClassicalWorkspace.Transport.liftWrite_key] using same

/-- Original caller inputs survive preparation and the ten retained cells. -/
def originalInputAfterTables {shape : CShape} (input : CInputRef base shape) :
    CInputRef (tableContext base noQuantum) shape :=
  (RetainedCells.transport (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256)).liftInput
      (originalInput base noQuantum input)

private def resultEntryPrefix {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (dimension : ℕ+) : Nat → List (RuntimeEntry kind)
  | 0 => []
  | count + 1 =>
      .storage (MeasurementCells.context ctx dimension count).canonicalFreshKey
        .retained (.finite dimension) :: resultEntryPrefix ctx dimension count

private lemma resultContext_entries {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).entries =
      resultEntryPrefix ctx dimension count ++ ctx.entries := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change .storage (MeasurementCells.context ctx dimension count).canonicalFreshKey
          .retained (.finite dimension) ::
          (MeasurementCells.context ctx dimension count).entries =
        (.storage (MeasurementCells.context ctx dimension count).canonicalFreshKey
          .retained (.finite dimension) :: resultEntryPrefix ctx dimension count) ++
          ctx.entries
      rw [List.cons_append, ih]

private lemma bankContext_entries :
    (bankContext base noQuantum).entries =
      .ownedLayout base.canonicalFreshKey
        (QubitLayout.canonical encoding.width).toQuantum :: base.entries := rfl

/-- The precise entries before the one original owned bank. -/
def beforeBank : List (RuntimeEntry .quantum) :=
  RetainedCells.entryPrefix (resultContext base noQuantum)
      (WindowTables.Outer.sharedShapes 256) ++
    resultEntryPrefix (bankContext base noQuantum) 2 520

/-- Retention prepends to, and never duplicates or moves, the original bank. -/
lemma tableContext_entries :
    (tableContext base noQuantum).entries =
      beforeBank base noQuantum ++
        .ownedLayout base.canonicalFreshKey
          (QubitLayout.canonical encoding.width).toQuantum :: base.entries := by
  calc
    (tableContext base noQuantum).entries =
        RetainedCells.entryPrefix (resultContext base noQuantum)
            (WindowTables.Outer.sharedShapes 256) ++
          (resultContext base noQuantum).entries :=
      RetainedCells.context_entries (resultContext base noQuantum)
        (WindowTables.Outer.sharedShapes 256)
    _ = RetainedCells.entryPrefix (resultContext base noQuantum)
            (WindowTables.Outer.sharedShapes 256) ++
          (resultEntryPrefix (bankContext base noQuantum) 2 520 ++
            (bankContext base noQuantum).entries) := by
      rw [resultContext, resultContext_entries]
    _ = RetainedCells.entryPrefix (resultContext base noQuantum)
            (WindowTables.Outer.sharedShapes 256) ++
          (resultEntryPrefix (bankContext base noQuantum) 2 520 ++
            (.ownedLayout base.canonicalFreshKey
              (QubitLayout.canonical encoding.width).toQuantum :: base.entries)) := by
      rw [bankContext_entries]
    _ = beforeBank base noQuantum ++
          .ownedLayout base.canonicalFreshKey
            (QubitLayout.canonical encoding.width).toQuantum :: base.entries := by
      rw [beforeBank, List.append_assoc]

private lemma tableContext_keys :
    (tableContext base noQuantum).keys =
      (beforeBank base noQuantum).map RuntimeEntry.key ++
        base.canonicalFreshKey :: base.entries.map RuntimeEntry.key := by
  unfold RuntimeCtx.keys
  rw [tableContext_entries base noQuantum]
  simp only [List.map_append, List.map_cons, RuntimeEntry.key]

/-- The full ordered quantum wire record is still the original 854-system bank. -/
lemma tableContext_wires :
    (QubitLayout.canonical encoding.width).toQuantum.wires =
      (tableContext base noQuantum).quantumLayout.wires := by
  calc
    (QubitLayout.canonical encoding.width).toQuantum.wires =
        (resultContext base noQuantum).quantumLayout.wires :=
      resultContext_wires base noQuantum
    _ = (tableContext base noQuantum).quantumLayout.wires :=
      (RetainedCells.context_quantumLayout_wires (resultContext base noQuantum)
        (WindowTables.Outer.sharedShapes 256)).symm

private def canonicalSliceKey (ctx : RuntimeCtx .quantum)
    (index : Fin 5) : StorageKey :=
  ⟨ctx.canonicalFreshKey.id + index.val⟩

private lemma canonicalSliceKey_fresh (ctx : RuntimeCtx .quantum) (index : Fin 5) :
    canonicalSliceKey ctx index ∉ ctx.keys := by
  intro member
  have memberIds : (canonicalSliceKey ctx index).id ∈ ctx.keys.map StorageKey.id :=
    List.mem_map_of_mem member
  have bounded : (canonicalSliceKey ctx index).id ≤
      (ctx.keys.map StorageKey.id).foldr Nat.max 0 :=
    List.le_max_of_le' 0 memberIds le_rfl
  change (ctx.keys.map StorageKey.id).foldr Nat.max 0 + 1 + index.val ≤
    (ctx.keys.map StorageKey.id).foldr Nat.max 0 at bounded
  omega

private lemma canonicalSliceKey_injective (ctx : RuntimeCtx .quantum) :
    Function.Injective (canonicalSliceKey ctx) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg StorageKey.id equal
  dsimp [canonicalSliceKey] at values
  omega

private def canonicalSliceKeyList (ctx : RuntimeCtx .quantum) : List StorageKey :=
  [canonicalSliceKey ctx 0, canonicalSliceKey ctx 1, canonicalSliceKey ctx 2,
    canonicalSliceKey ctx 3, canonicalSliceKey ctx 4]

private lemma canonicalSliceKeyList_nodup (ctx : RuntimeCtx .quantum) :
    (canonicalSliceKeyList ctx).Nodup := by
  simp only [canonicalSliceKeyList, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · intro h
    rcases h with h | h | h | h
    all_goals have := canonicalSliceKey_injective ctx h; omega
  constructor
  · intro h
    rcases h with h | h | h
    all_goals have := canonicalSliceKey_injective ctx h; omega
  constructor
  · intro h
    rcases h with h | h
    all_goals have := canonicalSliceKey_injective ctx h; omega
  constructor
  · intro h
    have := canonicalSliceKey_injective ctx h
    omega
  simp

private lemma canonicalSliceKeyList_fresh (ctx : RuntimeCtx .quantum) :
    ∀ key ∈ canonicalSliceKeyList ctx, key ∉ ctx.keys := by
  intro key member
  simp only [canonicalSliceKeyList, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals exact canonicalSliceKey_fresh ctx _

private lemma sliceEntryKeys (ctx : RuntimeCtx .quantum) :
    ((slices (canonicalSliceKey ctx)).map OwnedLayoutSlice.entry).map
        RuntimeEntry.key = canonicalSliceKeyList ctx := rfl

private lemma replaceOneNodup {α : Type} (oldKey : α) (before replacement after : List α)
    (old : (before ++ oldKey :: after).Nodup) (new : replacement.Nodup)
    (fresh : ∀ key ∈ replacement, key ∉ before ++ oldKey :: after) :
    (before ++ replacement ++ after).Nodup := by
  have beforeAfter : (before ++ after).Nodup :=
    (List.nodup_cons.mp (List.nodup_middle.mp old)).2
  have beforeNodup : before.Nodup := List.Nodup.of_append_left beforeAfter
  have afterNodup : after.Nodup := List.Nodup.of_append_right beforeAfter
  have beforeAfterDisjoint : before.Disjoint after :=
    List.disjoint_of_nodup_append beforeAfter
  have replacementAfter : replacement.Disjoint after := by
    intro key inReplacement inAfter
    exact fresh key inReplacement
      (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ inAfter)))
  have beforeReplacement : before.Disjoint replacement := by
    intro key inBefore inReplacement
    exact fresh key inReplacement (List.mem_append.mpr (Or.inl inBefore))
  have beforeRest : before.Disjoint (replacement ++ after) := by
    intro key inBefore inRest
    rcases List.mem_append.mp inRest with inReplacement | inAfter
    · exact beforeReplacement inBefore inReplacement
    · exact beforeAfterDisjoint inBefore inAfter
  simpa only [List.append_assoc] using
    beforeNodup.append (new.append afterNodup replacementAfter) beforeRest

/-- The full owned bank can be viewed after all 520 results and ten table cells. -/
def canonicalOwnedScope : OwnedScope (tableContext base noQuantum) where
  before := beforeBank base noQuantum
  after := base.entries
  bankKey := base.canonicalFreshKey
  originalEntries := tableContext_entries base noQuantum
  sliceKeys := canonicalSliceKey (tableContext base noQuantum)
  keysNodup := by
    let ctx := tableContext base noQuantum
    let before := (beforeBank base noQuantum).map RuntimeEntry.key
    let after := base.entries.map RuntimeEntry.key
    have prefixEq : ctx.keys = before ++ base.canonicalFreshKey :: after :=
      tableContext_keys base noQuantum
    have old : (before ++ base.canonicalFreshKey :: after).Nodup := by
      change ((beforeBank base noQuantum).map RuntimeEntry.key ++
        base.canonicalFreshKey :: base.entries.map RuntimeEntry.key).Nodup
      rw [← tableContext_keys base noQuantum]
      exact ctx.keysNodup
    have fresh : ∀ key ∈ canonicalSliceKeyList ctx,
        key ∉ before ++ base.canonicalFreshKey :: after := by
      intro key member
      have absent := canonicalSliceKeyList_fresh ctx key member
      exact Eq.mp
        (congrArg (fun keys : List StorageKey => key ∉ keys) prefixEq) absent
    have replaced := replaceOneNodup base.canonicalFreshKey before
      (canonicalSliceKeyList ctx) after old
        (canonicalSliceKeyList_nodup ctx) fresh
    simpa only [List.map_append, sliceEntryKeys] using replaced
  sameWires := tableContext_wires base noQuantum

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
