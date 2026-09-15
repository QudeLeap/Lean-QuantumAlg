/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Selection.Semantics
import all QuantumAlg.Algorithms.FiniteCyclicDLP.CallCountedRecovery.Native.Attempt.Correctness
import all QuantumAlg.Components.Classical.FirstAccepted.Option
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Complete first-success values of actual finite-cyclic recovery

The original selector folds the actual raw candidate and both flags together
with the checked group power. All samples are read in their original order,
including after an earlier acceptance. Actual allocation discharges scratch
separation and initializes the single persistent acceptance latch.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] {ctx : RuntimeCtx .quantum}

private def selectorKeys {width : Nat} (refs : FirstAccepted.Refs ctx width) :
    List StorageKey :=
  [refs.take.key, refs.available.key, refs.selected.key, refs.accepted.key]

private def optionValue {width : Nat} (value : Option (CShape.Word width)) :
    CShape.Value (.option (.unsignedWord width)) :=
  match value with
  | none => .optionNone
  | some word => .optionSome word

private def attemptOption (P : Parameters G)
    (input : CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CShape.Word P.width) : Option (CShape.Word P.width) :=
  if attemptAcceptedValue P input target then some (attemptCandidateValue P input) else none

/-- The original chronological first-success fold of the complete checked raw candidates. -/
def groupRecoveryValue (P : Parameters G) (count : Nat)
    (inputs : Fin count → CShape.Value (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CShape.Word P.width) : CShape.Value (.option (.unsignedWord P.width)) :=
  optionValue ((List.ofFn (fun index => attemptOption P (inputs index) target)).foldl
    FirstAccepted.retainFirst none)

private theorem selected_restrict {inner : RuntimeCtx .quantum} {width : Nat}
    (refs : FirstAccepted.Refs ctx width) (transport : Transport ctx inner)
    (store : Store inner) :
    FirstAccepted.selectedOption refs (transport.restrict store) =
      FirstAccepted.selectedOption (liftSelector refs transport) store := by
  simp only [FirstAccepted.selectedOption, liftSelector, FirstAccepted.cellRead,
    ← transport.liftWrite_input]
  rw [transport.workspaceTransport_restrict_readsAs,
    transport.workspaceTransport_restrict_readsAs]
  congr 1

private theorem select_correct (P : Parameters G)
    (input : CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (distinct : (selectorKeys refs).Nodup) :
    ∃ record : Store ctx → Store ctx × (selectAttempt P input target refs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (selectAttempt P input target refs).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        FirstAccepted.selectedOption refs (record before).1 =
          FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before)
            (attemptOption P (before.read input) (before.read target)) ∧
        ∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
          (record before).1.read other = before.read other := by
  apply groupAttempt_actualRecord_correct P input target _
    (fun before after candidate eligible =>
      FirstAccepted.selectedOption refs after =
        FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before)
          (if eligible then some candidate else none) ∧
      ∀ {shape : CShape} (other : CInputRef ctx shape),
        (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) → after.read other = before.read other)
  intro inner candidate accepted transport candidateFree acceptedFree
  let lifted := liftSelector refs transport
  let inputs : FirstAccepted.Inputs inner P.width := ⟨accepted, candidate⟩
  refine ⟨FirstAccepted.step inputs lifted,
    FirstAccepted.firstAccepted_execute inputs lifted, ?_⟩
  intro before
  have separate : FirstAccepted.Separated inputs lifted := by
    constructor
    · intro present
      have absent := acceptedFree _ present (FirstAccepted.cellRead refs.available)
      apply absent
      simp [lifted, liftSelector, FirstAccepted.cellRead, transport.liftWrite_key,
        transport.liftInput_storageKeys, CInputRef.storageKeys]
    · intro present
      have absent := candidateFree _ present (FirstAccepted.cellRead refs.available)
      apply absent
      simp [lifted, liftSelector, FirstAccepted.cellRead, transport.liftWrite_key,
        transport.liftInput_storageKeys, CInputRef.storageKeys]
    · intro present
      have absent := candidateFree _ present (FirstAccepted.cellRead refs.take)
      apply absent
      simp [lifted, liftSelector, FirstAccepted.cellRead, transport.liftWrite_key,
        transport.liftInput_storageKeys, CInputRef.storageKeys]
    all_goals
      simp only [lifted, liftSelector, transport.liftWrite_key]
      intro same
      simp [selectorKeys, same] at distinct
  refine ⟨?_, ?_⟩
  · rw [selected_restrict, selected_restrict]
    exact FirstAccepted.firstAccepted_selectedOption inputs lifted separate before
  · intro shape other avoids
    have frame := FirstAccepted.firstAccepted_read_other inputs lifted
      (transport.liftInput other)
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using avoids refs.available.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using avoids refs.take.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using avoids refs.accepted.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using avoids refs.selected.key (by simp [selectorKeys]))
      before
    exact (transport.workspaceTransport_restrict_readsAs
      (FirstAccepted.step inputs lifted before).1 other).symm.trans
        (frame.trans (transport.workspaceTransport_restrict_readsAs before other))

private theorem loop_store (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width)) (refs : FirstAccepted.Refs ctx P.width)
    (sampleFree : ∀ index key, key ∈ selectorKeys refs → key ∉ (samples index).storageKeys)
    (targetFree : ∀ key ∈ selectorKeys refs, key ∉ target.storageKeys)
    (records : ∀ index, Store ctx → Store ctx × (selectAttempt P (samples index) target refs).Path)
    (values : ∀ index before,
      FirstAccepted.selectedOption refs (records index before).1 =
        FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before)
          (attemptOption P (before.read (samples index)) (before.read target)) ∧
      ∀ {shape : CShape} (other : CInputRef ctx shape),
        (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
        (records index before).1.read other = before.read other)
    (before : Store ctx) :
    let after := (Circuit.forRangeRecord count
      (fun index => selectAttempt P (samples index) target refs) records before).1
    FirstAccepted.selectedOption refs after =
      (List.ofFn (fun index => attemptOption P (before.read (samples index))
        (before.read target))).foldl FirstAccepted.retainFirst
          (FirstAccepted.selectedOption refs before) ∧
    ∀ {shape : CShape} (other : CInputRef ctx shape),
      (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
      after.read other = before.read other := by
  induction count generalizing before with
  | zero => exact ⟨rfl, by intros; rfl⟩
  | succ count ih =>
      have head := values 0 before
      have tail := ih (fun index => samples index.succ)
        (fun index key present => sampleFree index.succ key present)
        (fun index => records index.succ) (fun index => values index.succ)
        (records 0 before).1
      have sampleRead : ∀ index, (records 0 before).1.read (samples index) =
          before.read (samples index) := fun index => head.2 _ (sampleFree index)
      have targetRead := head.2 target targetFree
      dsimp only [Circuit.forRangeRecord, Circuit.sequenceRecord]
      refine ⟨?_, ?_⟩
      · rw [tail.1, head.1, List.ofFn_succ, List.foldl_cons]
        simp only [sampleRead, targetRead]
      · intro shape other avoids
        exact (tail.2 other avoids).trans (head.2 other avoids)

private theorem selectorKeys_cells {width : Nat} (cells : Cells ctx (selectorShapes width)) :
    selectorKeys (selectorRefs cells) = cells.keys := by
  cases cells with
  | cons take rest =>
      cases rest with
      | cons available rest =>
          cases rest with
          | cons selected rest =>
              cases rest with
              | cons accepted rest => cases rest; rfl

private theorem selected_initialized {width : Nat} (cells : Cells ctx (selectorShapes width))
    (store : Store ctx) (initialized : cells.Initialized store) :
    FirstAccepted.selectedOption (selectorRefs cells) store = none := by
  cases cells with
  | cons take rest =>
      cases rest with
      | cons available rest =>
          cases rest with
          | cons selected rest =>
              cases rest with
              | cons accepted rest =>
                  cases rest
                  simp only [Cells.Initialized] at initialized
                  simp only [selectorRefs, Cells.head, Cells.tail,
                    FirstAccepted.selectedOption, FirstAccepted.cellRead,
                    initialized.2.2.2.1, CShape.initialValue, CShape.Value.toBool,
                    Bool.false_eq_true, if_false]

private theorem pack_store {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    store.applyOp (selectionPack refs output) =
      store.write output (optionValue (FirstAccepted.selectedOption refs store)) := by
  change store.write output (CShape.packOption
    (.product (store.read (FirstAccepted.cellRead refs.accepted))
      (store.read (FirstAccepted.cellRead refs.selected)))) = _
  cases value : store.read (FirstAccepted.cellRead refs.accepted) with
  | bit accepted =>
      cases accepted <;>
        simp only [FirstAccepted.selectedOption, value, CShape.Value.toBool,
          optionValue, CShape.packOption, Bool.false_eq_true, eq_self, if_false, if_true]

private def packStep {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    Store ctx × (Circuit.classical (selectionPack refs output)).Path :=
  (store.applyOp (selectionPack refs output), ())

private theorem packStep_execute {width : Nat} (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.classical (selectionPack refs output)).execute Reference state =
      state.mapClassical (fun entry =>
        ((packStep refs output entry.1).1, (entry.2, (packStep refs output entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical _ Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The same complete actual record writes exactly the first checked candidate to the caller.

The four real selector initializations and every temporary allocation are
internal. Samples, target and output may share original caller storage; all
sample reads precede the single final output write. The equality specifies
the entire final Store and retains arbitrary reference blocks and history.
-/
theorem groupRecoveryInto_actualRecord_correct (P : Parameters G) (count : Nat)
    (samples : Fin count → CInputRef ctx (.fixedVector (P.width + P.width) (.finite 2)))
    (target : CInputRef ctx (.unsignedWord P.width))
    (output : CWriteRef ctx (.option (.unsignedWord P.width))) :
    ∃ record : Store ctx → Store ctx × (recoveryInto P count samples target output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (recoveryInto P count samples target output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, (record before).1 = before.write output
        (groupRecoveryValue P count (fun index => before.read (samples index))
          (before.read target)) := by
  apply withCells_actualRecord_initialized_restricted_post ctx (selectorShapes P.width)
    (fun cells _ transport _ =>
      recoveryBody P count (fun index => transport.liftInput (samples index))
        (transport.liftInput target) (selectorRefs cells) (transport.liftWrite output))
    (fun before after => after = before.write output
      (groupRecoveryValue P count (fun index => before.read (samples index)) (before.read target)))
  intro inner cells distinct transport separated
  let refs := selectorRefs cells
  let inputs := fun index => transport.liftInput (samples index)
  let target' := transport.liftInput target
  have different : (selectorKeys refs).Nodup := by
    rw [selectorKeys_cells]
    exact cells.workspaceCells_distinct_keys_nodup distinct
  have free : ∀ key ∈ selectorKeys refs, ∀ {shape : CShape} (other : CInputRef ctx shape),
      key ∉ (transport.liftInput other).storageKeys := by
    intro key present shape other
    have actual : key ∈ cells.keys := by simpa only [refs, selectorKeys_cells] using present
    exact cells.workspaceCells_transportSeparated_avoids_of_mem transport separated actual other
  have each := fun index => select_correct P (inputs index) target' refs different
  choose records equations values using each
  let loop := selectionLoop P count inputs target' refs
  let first := Circuit.forRangeRecord count
    (fun index => selectAttempt P (inputs index) target' refs) records
  let pack := Circuit.classical (selectionPack refs (transport.liftWrite output))
  refine ⟨Circuit.sequenceRecord loop pack first (packStep refs (transport.liftWrite output)),
    Circuit.execute_sequenceRecord loop pack first (packStep refs (transport.liftWrite output))
      (Circuit.execute_forRangeRecord count _ records equations)
      (packStep_execute refs (transport.liftWrite output)), ?_⟩
  intro before initialized
  have actual := loop_store P count inputs target' refs
    (fun index key present => free key present (samples index))
    (fun key present => free key present target) records values before
  have original : transport.restrict (first before).1 = transport.restrict before := by
    apply transport.workspaceTransport_readsAs_restrict_iff.mp
    intro shape other
    exact (actual.2 (transport.liftInput other) (fun key present => free key present other)).trans
      (transport.workspaceTransport_restrict_readsAs before other)
  have selected := actual.1
  rw [selected_initialized cells before initialized] at selected
  change transport.restrict ((first before).1.applyOp
    (selectionPack refs (transport.liftWrite output))) = _
  rw [pack_store, transport.workspaceTransport_restrict_write, original, selected]
  have reads : ∀ {shape : CShape} (other : CInputRef ctx shape),
      before.read (transport.liftInput other) = (transport.restrict before).read other :=
    transport.workspaceTransport_restrict_readsAs before
  simp only [groupRecoveryValue, inputs, target', reads]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.CallCountedRecovery.Native
