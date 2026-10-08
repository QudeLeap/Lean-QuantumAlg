/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Values
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Values
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Option
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Actual value written by known-order recovery selection

The same chronological record used by the interpreter writes the pure
`recoveryValue`. Every sample is still executed after an earlier acceptance,
so hidden oracle state and all query paths remain part of the real execution.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

open Execution ClassicalWorkspace ClassicalRoutines

noncomputable section

attribute [local instance] Classical.decEq

universe u

variable {G : Type u} [Group G] [Fintype G] {ctx : RuntimeCtx .quantum}

private def selectorKeys {width : Nat} (refs : FirstAccepted.Refs ctx width) :
    List StorageKey :=
  [refs.take.key, refs.available.key, refs.selected.key, refs.accepted.key]

private def optionValue {width : Nat} (value : Option (CShape.Word width)) :
    CShape.Value (.option (.unsignedWord width)) :=
  match value with
  | none => .optionNone
  | some word => .optionSome word

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

private theorem select_correct (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (input : CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (distinct : (selectorKeys refs).Nodup) :
    ∃ record : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (selectAttempt P spec input refs).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (selectAttempt P spec input refs).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × (OrderExecution.model P).HiddenState,
        FirstAccepted.selectedOption refs (record before).1.1 =
          FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before.1)
            (attemptOption P spec (before.1.read input)) ∧
        ∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
          (record before).1.1.read other = before.1.read other := by
  unfold selectAttempt
  apply withAttempt_actualRecord_correct P spec input _
    (fun before after candidate eligible =>
      FirstAccepted.selectedOption refs after =
        FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before)
          (if eligible then some candidate else none) ∧
      ∀ {shape : CShape} (other : CInputRef ctx shape),
        (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
        after.read other = before.read other)
  intro inner candidate accepted transport candidateFree acceptedFree
  let lifted := liftSelector refs transport
  let inputs : FirstAccepted.Inputs inner (OrderPreparation.width P) :=
    ⟨accepted, candidate⟩
  refine ⟨fun entry =>
      let result := FirstAccepted.step (model := OrderExecution.model P) inputs lifted entry.1
      ((result.1, entry.2), result.2),
    ?_, ?_⟩
  · intro Reference History _ state
    exact (FirstAccepted.firstAccepted_execute
      (model := OrderExecution.model P) inputs lifted Reference state).trans
        (mapClassicalExplicit_eq state _).symm
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
    exact FirstAccepted.firstAccepted_selectedOption
      (model := OrderExecution.model P) (ctx := inner)
      (width := OrderPreparation.width P) inputs lifted separate before.1
  · intro shape other avoids
    have frame := FirstAccepted.firstAccepted_read_other
      (model := OrderExecution.model P) (ctx := inner)
      (width := OrderPreparation.width P) inputs lifted
      (transport.liftInput other)
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using
          avoids refs.available.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using
          avoids refs.take.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using
          avoids refs.accepted.key (by simp [selectorKeys]))
      (by simpa only [lifted, liftSelector, transport.liftWrite_key,
        transport.liftInput_storageKeys] using
          avoids refs.selected.key (by simp [selectorKeys]))
      before.1
    exact (transport.workspaceTransport_restrict_readsAs
      (FirstAccepted.step (model := OrderExecution.model P) inputs lifted before.1).1
      other).symm.trans
        (frame.trans (transport.workspaceTransport_restrict_readsAs before.1 other))

private theorem loop_store (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (refs : FirstAccepted.Refs ctx (OrderPreparation.width P))
    (sampleFree : ∀ index key, key ∈ selectorKeys refs →
      key ∉ (samples index).storageKeys)
    (records : ∀ index, Store ctx × (OrderExecution.model P).HiddenState →
      (Store ctx × (OrderExecution.model P).HiddenState) ×
        (selectAttempt P spec (samples index) refs).Path)
    (values : ∀ index before,
      FirstAccepted.selectedOption refs (records index before).1.1 =
        FirstAccepted.retainFirst (FirstAccepted.selectedOption refs before.1)
          (attemptOption P spec (before.1.read (samples index))) ∧
      ∀ {shape : CShape} (other : CInputRef ctx shape),
        (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
        (records index before).1.1.read other = before.1.read other)
    (before : Store ctx × (OrderExecution.model P).HiddenState) :
    let after := (Circuit.forRangeRecord count
      (fun index => selectAttempt P spec (samples index) refs) records before).1
    FirstAccepted.selectedOption refs after.1 =
      (List.ofFn (fun index => attemptOption P spec
        (before.1.read (samples index)))).foldl FirstAccepted.retainFirst
          (FirstAccepted.selectedOption refs before.1) ∧
    ∀ {shape : CShape} (other : CInputRef ctx shape),
      (∀ key ∈ selectorKeys refs, key ∉ other.storageKeys) →
      after.1.read other = before.1.read other := by
  induction count generalizing before with
  | zero => exact ⟨rfl, by intros; rfl⟩
  | succ count ih =>
      have head := values 0 before
      have tail := ih (fun index => samples index.succ)
        (fun index key present => sampleFree index.succ key present)
        (fun index => records index.succ) (fun index => values index.succ)
        (records 0 before).1
      have sampleRead : ∀ index, (records 0 before).1.1.read (samples index) =
          before.1.read (samples index) :=
        fun index => head.2 _ (sampleFree index)
      dsimp only [Circuit.forRangeRecord, Circuit.sequenceRecord]
      refine ⟨?_, ?_⟩
      · rw [tail.1, head.1, List.ofFn_succ, List.foldl_cons]
        simp only [sampleRead]
      · intro shape other avoids
        exact (tail.2 other avoids).trans (head.2 other avoids)

private theorem selectorKeys_cells {width : Nat}
    (cells : Cells ctx (selectorShapes width)) :
    selectorKeys (selectorRefs cells) = cells.keys := by
  cases cells with
  | cons take rest =>
      cases rest with
      | cons available rest =>
          cases rest with
          | cons selected rest =>
              cases rest with
              | cons accepted rest => cases rest; rfl

private theorem selected_initialized {width : Nat}
    (cells : Cells ctx (selectorShapes width)) (store : Store ctx)
    (initialized : cells.Initialized store) :
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

private theorem pack_store {width : Nat}
    (refs : FirstAccepted.Refs ctx width)
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

private def packStep (P : KnownOrderProblem G) {width : Nat}
    (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (entry : Store ctx × (OrderExecution.model P).HiddenState) :
    (Store ctx × (OrderExecution.model P).HiddenState) ×
      (BitWord.instruction (execution := OrderExecution.model P)
        (selectionPack refs output)).Path :=
  let result := BitWord.instructionStep (execution := OrderExecution.model P)
    (selectionPack refs output) entry.1
  ((result.1, entry.2), result.2)

private theorem packStep_execute (P : KnownOrderProblem G) {width : Nat}
    (refs : FirstAccepted.Refs ctx width)
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)) :
    (BitWord.instruction (execution := OrderExecution.model P)
      (selectionPack refs output)).execute Reference state =
      state.mapClassical (fun entry =>
        let result := packStep P refs output (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  exact BitWord.bitWord_instruction_execute
    (execution := OrderExecution.model P) (selectionPack refs output) state

/-- The complete actual recovery record writes exactly its pure chronological value. -/
public theorem recoveryInto_actualRecord_correct (P : KnownOrderProblem G)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec (OrderPreparation.width P))
    (count : Nat)
    (samples : Fin count → CInputRef ctx
      (.fixedVector (OrderPreparation.width P + OrderPreparation.width P) (.finite 2)))
    (output : CWriteRef ctx
      (.option (.unsignedWord (OrderPreparation.width P)))) :
    ∃ record : Store ctx × (OrderExecution.model P).HiddenState →
        (Store ctx × (OrderExecution.model P).HiddenState) ×
          (recoveryInto P spec count samples output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference ((OrderExecution.model P).HiddenState × History)),
        (recoveryInto P spec count samples output).execute Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × (OrderExecution.model P).HiddenState,
        (record before).1.1 = before.1.write output
          (recoveryValue P spec count (fun index => before.1.read (samples index))) := by
  apply withCells_actualRecord_initialized_restricted_post
    (model := OrderExecution.model P) ctx
    (selectorShapes (OrderPreparation.width P))
    (fun cells _ transport _ =>
      recoveryBody P spec count (fun index => transport.liftInput (samples index))
        (selectorRefs cells) (transport.liftWrite output))
    (fun before after => after = before.write output
      (recoveryValue P spec count (fun index => before.read (samples index))))
  intro inner cells distinct transport separated
  let refs := selectorRefs cells
  let inputs := fun index => transport.liftInput (samples index)
  have different : (selectorKeys refs).Nodup := by
    rw [selectorKeys_cells]
    exact cells.workspaceCells_distinct_keys_nodup distinct
  have free : ∀ key ∈ selectorKeys refs,
      ∀ {shape : CShape} (other : CInputRef ctx shape),
        key ∉ (transport.liftInput other).storageKeys := by
    intro key present shape other
    have actual : key ∈ cells.keys := by
      simpa only [refs, selectorKeys_cells] using present
    exact cells.workspaceCells_transportSeparated_avoids_of_mem
      transport separated actual other
  have each := fun index => select_correct P spec (inputs index) refs different
  choose records equations values using each
  let loop := selectionLoop P spec count inputs refs
  let first := Circuit.forRangeRecord count
    (fun index => selectAttempt P spec (inputs index) refs) records
  let pack := BitWord.instruction (execution := OrderExecution.model P)
    (selectionPack refs (transport.liftWrite output))
  refine ⟨Circuit.sequenceRecord loop pack first
      (packStep P refs (transport.liftWrite output)),
    Circuit.execute_sequenceRecord loop pack first
      (packStep P refs (transport.liftWrite output))
      (Circuit.execute_forRangeRecord count _ records equations)
      (packStep_execute P refs (transport.liftWrite output)), ?_⟩
  intro before initialized
  have actual := loop_store P spec count inputs refs
    (fun index key present => free key present (samples index))
    records values before
  have original : transport.restrict (first before).1.1 =
      transport.restrict before.1 := by
    apply transport.workspaceTransport_readsAs_restrict_iff.mp
    intro shape other
    exact (actual.2 (transport.liftInput other)
      (fun key present => free key present other)).trans
        (transport.workspaceTransport_restrict_readsAs before.1 other)
  have selected := actual.1
  rw [selected_initialized cells before.1 initialized] at selected
  change transport.restrict ((first before).1.1.applyOp
    (selectionPack refs (transport.liftWrite output))) = _
  rw [pack_store, transport.workspaceTransport_restrict_write, original, selected]
  have reads : ∀ {shape : CShape} (other : CInputRef ctx shape),
      before.1.read (transport.liftInput other) =
        (transport.restrict before.1).read other :=
    transport.workspaceTransport_restrict_readsAs before.1
  have optionReads :
      (fun index => attemptOption P spec (before.1.read (inputs index))) =
        (fun index => attemptOption P spec
          ((transport.restrict before.1).read (samples index))) := by
    funext index
    apply congrArg (attemptOption P spec)
    simpa only [inputs] using reads (samples index)
  rw [optionReads]
  unfold recoveryValue optionValue
  cases (List.ofFn fun index =>
    attemptOption P spec ((transport.restrict before.1).read (samples index))).foldl
      FirstAccepted.retainFirst none <;> rfl

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
