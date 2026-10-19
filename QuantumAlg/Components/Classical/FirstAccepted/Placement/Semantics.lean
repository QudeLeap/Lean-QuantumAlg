/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Placement
import all QuantumAlg.Components.Classical.FirstAccepted.StoreSemantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write

/-!
# Full-state semantics of the original allocated selector

The two real scratch writes derive the stored take bit from the incoming
persistent latch and eligibility. The selected branch performs its original
word write before the acceptance write. Both private bits are then released.
The complete caller store and every quantum-reference block follow this same
actual record, including when caller inputs alias persistent destinations.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual selected branch writes the word before its acceptance latch. -/
def selectionWrite (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width)) (before : Store ctx) : Store ctx :=
  if (!(before.read (cellRead accepted)).toBool) && (before.read inputs.eligible).toBool then
    (before.write selected (before.read inputs.candidate)).write accepted (.bit true)
  else before

private lemma scratch_free {inner : RuntimeCtx kind} (cells : Cells inner [.bit, .bit])
    (transport : Transport ctx inner) (separated : cells.TransportSeparated transport)
    {shape : CShape} (input : CInputRef ctx shape) :
    cells.tail.head.ref.key ∉ (transport.liftInput input).storageKeys ∧
      cells.head.ref.key ∉ (transport.liftInput input).storageKeys := by
  cases cells with
  | cons take rest =>
    cases rest with
    | cons available rest =>
      cases rest
      exact ⟨separated.2.1 input, separated.1 input⟩

private lemma copyStore_write (inputs : Inputs ctx width) (refs : Refs ctx width)
    (selectedTake : refs.selected.key ≠ refs.take.key) (before : Store ctx) :
    copyStore inputs refs before =
      (before.write refs.selected (before.read inputs.candidate)).write refs.accepted
        (before.read (cellRead refs.take)) := by
  change (before.write refs.selected (before.read inputs.candidate)).write refs.accepted
    ((before.write refs.selected (before.read inputs.candidate)).read (cellRead refs.take)) = _
  have unchanged := Store.read_write_other before refs.selected refs.take.toCStorageRef
    (before.read inputs.candidate) selectedTake
  exact congrArg (fun value =>
    (before.write refs.selected (before.read inputs.candidate)).write refs.accepted value) unchanged

private lemma bit_value (value : CShape.Value .bit) : .bit value.toBool = value := by
  cases value
  rfl

/-- Actual two-bit allocation leaves exactly the original conditional pair of caller writes. -/
lemma withSelection_actualRecord {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (withSelection
      (model := model) inputs accepted selected).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withSelection (model := model) inputs accepted selected).execute
          environment Reference state =
          state.mapClassical (fun entry =>
            let actual := record (entry.1, entry.2.1)
            (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (record before).1.1 = selectionWrite inputs accepted selected before.1 := by
  unfold withSelection
  apply withCells_actualRecord_initialized_post (environment := environment) ctx [.bit, .bit]
    (fun cells _ transport _ =>
      circuit (model := model) (placedInputs inputs transport) (placedRefs cells transport accepted
        selected))
    (fun before after => after = selectionWrite inputs accepted selected before)
  intro inner cells _distinct transport separated
  let innerInputs := placedInputs inputs transport
  let refs := placedRefs cells transport accepted selected
  refine ⟨fun before =>
    let actual := step (model := model) innerInputs refs before.1
    ((actual.1, before.2), actual.2), ?_, ?_⟩
  · intro reference history _ state
    exact (firstAccepted_execute innerInputs refs reference state).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  intro source entry reads _initialized
  rcases entry with ⟨before, hidden⟩
  let decision := decisionStore innerInputs refs before
  have decisionReads : transport.ReadsAs source decision := by
    intro shape other
    exact ((Store.read_applyOp_of_not_mem_storageKeys _ (takeOp innerInputs refs)
      (transport.liftInput other) (scratch_free cells transport separated other).2).trans
      (Store.read_applyOp_of_not_mem_storageKeys _ (availableOp refs)
        (transport.liftInput other) (scratch_free cells transport separated other).1)).trans
      (reads other)
  have inputAccepted : before.read (cellRead refs.accepted) =
      source.read (cellRead accepted) := by
    simpa only [refs, placedRefs, cellRead, transport.liftWrite_input]
      using reads (cellRead accepted)
  have takeValue : (decision.read (cellRead refs.take)).toBool =
      ((!(source.read (cellRead accepted)).toBool) && (source.read inputs.eligible).toBool) := by
    exact (firstAccepted_decision_take innerInputs refs
      (scratch_free cells transport separated inputs.eligible).1 before).trans
      (by
        change (!(before.read (cellRead refs.accepted)).toBool &&
          (before.read (transport.liftInput inputs.eligible)).toBool) = _
        rw [inputAccepted, reads inputs.eligible])
  have selectedTake : refs.selected.key ≠ refs.take.key := by
    have free := (scratch_free cells transport separated (cellRead selected)).2
    have different : cells.head.ref.key ≠ selected.key := by
      simpa only [transport.liftInput_storageKeys, cellRead, CInputRef.storageKeys,
        List.mem_singleton] using free
    simpa only [refs, placedRefs, transport.liftWrite_key] using different.symm
  refine ⟨selectionWrite inputs accepted selected source, rfl, ?_⟩
  intro shape other
  rw [firstAccepted_step_store]
  change (if (decision.read (cellRead refs.take)).toBool then copyStore innerInputs refs decision
      else decision).read (transport.liftInput other) =
    (selectionWrite inputs accepted selected source).read other
  by_cases taken : ((!(source.read (cellRead accepted)).toBool) &&
      (source.read inputs.eligible).toBool) = true
  · have actualTaken : (decision.read (cellRead refs.take)).toBool = true :=
      takeValue.trans taken
    rw [if_pos actualTaken, copyStore_write innerInputs refs selectedTake]
    have actualBit : decision.read (cellRead refs.take) = .bit true := by
      rw [← bit_value (decision.read (cellRead refs.take)), actualTaken]
    have candidateRead : decision.read innerInputs.candidate = source.read inputs.candidate :=
      decisionReads inputs.candidate
    rw [actualBit, candidateRead, selectionWrite, if_pos taken]
    exact transport.workspaceTransport_readsAs_write
      (transport.workspaceTransport_readsAs_write decisionReads selected
        (source.read inputs.candidate)) accepted (.bit true) other
  · have skipped : (decision.read (cellRead refs.take)).toBool ≠ true := by
      rw [takeValue]
      exact taken
    rw [if_neg skipped, selectionWrite, if_neg taken]
    exact decisionReads other

/-- Original first acceptance gives the OR latch and preserves the first selected word. -/
lemma selectionWrite_latches (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width))
    (different : accepted.key ≠ selected.key) (before : Store ctx) :
    ((selectionWrite inputs accepted selected before).read (cellRead accepted)).toBool =
        ((before.read (cellRead accepted)).toBool || (before.read inputs.eligible).toBool) ∧
      (selectionWrite inputs accepted selected before).read (cellRead selected) =
        if (!(before.read (cellRead accepted)).toBool) &&
            (before.read inputs.eligible).toBool then
          before.read inputs.candidate else before.read (cellRead selected) := by
  unfold selectionWrite
  by_cases taken : ((!(before.read (cellRead accepted)).toBool) &&
      (before.read inputs.eligible).toBool) = true
  · rw [if_pos taken]
    simp only [cellRead, Store.read_write_same,
      Store.read_write_other _ _ _ _ different]
    exact ⟨taken.symm.trans (latch_when_taken _ _ taken), (if_pos taken).symm⟩
  · rw [if_neg taken]
    exact ⟨latch_when_skipped _ _ taken, (if_neg taken).symm⟩

/-- Every actual caller read outside both persistent outputs is retained. -/
lemma selectionWrite_read_other (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width)) (before : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (acceptedFree : accepted.key ∉ other.storageKeys)
    (selectedFree : selected.key ∉ other.storageKeys) :
    (selectionWrite inputs accepted selected before).read other = before.read other := by
  unfold selectionWrite
  split
  · rw [Store.read_write_of_not_mem_storageKeys _ _ _ other acceptedFree,
      Store.read_write_of_not_mem_storageKeys _ _ _ other selectedFree]
  · rfl

end

end QuantumAlg.ClassicalRoutines.FirstAccepted
