/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Owned

/-!
# Location of the owned point-window bank in an extended context

The original owned bank may follow retained or lexical storage entries. This
module tracks its exact position and chooses five fresh view keys in the full
current context. The conversion to `OwnedScope` preserves the bank and its
physical wires.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open QuantumAlg.Execution

/-- The exact position of the original owned bank in an arbitrary current context. -/
structure BankLocation (ctx : RuntimeCtx .quantum) where
  /-- Entries preceding the original owned bank in this context. -/
  before : List (RuntimeEntry .quantum)
  /-- Entries following the original owned bank in this context. -/
  after : List (RuntimeEntry .quantum)
  /-- Storage key of the original owned bank. -/
  bankKey : StorageKey
  /-- The complete entry-list position of that bank. -/
  entries : ctx.entries = before ++
    .ownedLayout bankKey (QubitLayout.canonical encoding.width).toQuantum :: after
  /-- The bank's physical wires equal the current quantum-layout wires. -/
  sameWires :
    (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires

namespace BankLocation

variable {ctx : RuntimeCtx .quantum}

/-- Forget old slice names but retain the actual owned-bank position and wires. -/
def ofOwnedScope (scope : OwnedScope ctx) : BankLocation ctx where
  before := scope.before
  after := scope.after
  bankKey := scope.bankKey
  entries := scope.originalEntries
  sameWires := scope.sameWires

private def sliceKey (ctx : RuntimeCtx .quantum) (index : Fin 5) : StorageKey :=
  ⟨ctx.canonicalFreshKey.id + index.val⟩

private lemma sliceKey_fresh (ctx : RuntimeCtx .quantum) (index : Fin 5) :
    sliceKey ctx index ∉ ctx.keys := by
  intro member
  have memberIds : (sliceKey ctx index).id ∈ ctx.keys.map StorageKey.id :=
    List.mem_map_of_mem member
  have bounded : (sliceKey ctx index).id ≤
      (ctx.keys.map StorageKey.id).foldr Nat.max 0 :=
    List.le_max_of_le' 0 memberIds le_rfl
  change (ctx.keys.map StorageKey.id).foldr Nat.max 0 + 1 + index.val ≤
    (ctx.keys.map StorageKey.id).foldr Nat.max 0 at bounded
  omega

private lemma sliceKey_injective (ctx : RuntimeCtx .quantum) :
    Function.Injective (sliceKey ctx) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg StorageKey.id equal
  dsimp [sliceKey] at values
  omega

private def sliceKeyList (ctx : RuntimeCtx .quantum) : List StorageKey :=
  [sliceKey ctx 0, sliceKey ctx 1, sliceKey ctx 2,
    sliceKey ctx 3, sliceKey ctx 4]

private lemma sliceKeyList_nodup (ctx : RuntimeCtx .quantum) :
    (sliceKeyList ctx).Nodup := by
  simp only [sliceKeyList, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false]
  constructor
  · intro h
    rcases h with h | h | h | h
    all_goals have := sliceKey_injective ctx h; omega
  constructor
  · intro h
    rcases h with h | h | h
    all_goals have := sliceKey_injective ctx h; omega
  constructor
  · intro h
    rcases h with h | h
    all_goals have := sliceKey_injective ctx h; omega
  constructor
  · intro h
    have := sliceKey_injective ctx h
    omega
  simp

private lemma sliceKeyList_fresh (ctx : RuntimeCtx .quantum) :
    ∀ key ∈ sliceKeyList ctx, key ∉ ctx.keys := by
  intro key member
  simp only [sliceKeyList, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals exact sliceKey_fresh ctx _

private lemma sliceEntryKeys (ctx : RuntimeCtx .quantum) :
    ((slices (sliceKey ctx)).map OwnedLayoutSlice.entry).map
        RuntimeEntry.key = sliceKeyList ctx := rfl

private lemma replaceOneNodup {α : Type} (oldKey : α)
    (before replacement after : List α)
    (old : (before ++ oldKey :: after).Nodup)
    (new : replacement.Nodup)
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

variable (location : BankLocation ctx)

/-- Choose five view keys fresh for this complete context, not an earlier one. -/
def toOwnedScope : OwnedScope ctx where
  before := location.before
  after := location.after
  bankKey := location.bankKey
  originalEntries := location.entries
  sliceKeys := sliceKey ctx
  keysNodup := by
    let before := location.before.map RuntimeEntry.key
    let after := location.after.map RuntimeEntry.key
    have prefixEq : ctx.keys = before ++ location.bankKey :: after := by
      unfold RuntimeCtx.keys
      rw [location.entries]
      simp only [List.map_append, List.map_cons, RuntimeEntry.key]
      rfl
    have old : (before ++ location.bankKey :: after).Nodup := by
      rw [← prefixEq]
      exact ctx.keysNodup
    have fresh : ∀ key ∈ sliceKeyList ctx,
        key ∉ before ++ location.bankKey :: after := by
      intro key member
      have absent := sliceKeyList_fresh ctx key member
      exact Eq.mp
        (congrArg (fun keys : List StorageKey => key ∉ keys) prefixEq) absent
    have replaced := replaceOneNodup location.bankKey before
      (sliceKeyList ctx) after old (sliceKeyList_nodup ctx) fresh
    simpa only [List.map_append, sliceEntryKeys] using replaced
  sameWires := location.sameWires

/-- A new lexical cell precedes the same owned bank without moving its wires. -/
def underWorkspace (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    BankLocation (ctx.addWorkspace key shape fresh) where
  before := .storage key .workspace shape :: location.before
  after := location.after
  bankKey := location.bankKey
  entries := by
    change .storage key .workspace shape :: ctx.entries =
      (.storage key .workspace shape :: location.before) ++
        .ownedLayout location.bankKey
          (QubitLayout.canonical encoding.width).toQuantum :: location.after
    rw [location.entries]
    rfl
  sameWires := by
    calc
      (QubitLayout.canonical encoding.width).toQuantum.wires =
          ctx.quantumLayout.wires := location.sameWires
      _ = (ctx.addWorkspace key shape fresh).quantumLayout.wires := by
        rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires,
          RuntimeCtx.quantumWires_addWorkspace]

/-- The same location also survives a paid retained classical cell. -/
def underRetained (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    BankLocation (ctx.addRetained key shape fresh) where
  before := .storage key .retained shape :: location.before
  after := location.after
  bankKey := location.bankKey
  entries := by
    change .storage key .retained shape :: ctx.entries =
      (.storage key .retained shape :: location.before) ++
        .ownedLayout location.bankKey
          (QubitLayout.canonical encoding.width).toQuantum :: location.after
    rw [location.entries]
    rfl
  sameWires := by
    calc
      (QubitLayout.canonical encoding.width).toQuantum.wires =
          ctx.quantumLayout.wires := location.sameWires
      _ = (ctx.addRetained key shape fresh).quantumLayout.wires := by
        rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires,
          RuntimeCtx.quantumWires_addRetained]

end BankLocation

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
