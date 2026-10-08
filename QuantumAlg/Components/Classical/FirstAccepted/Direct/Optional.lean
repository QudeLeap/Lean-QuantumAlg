/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# First-success selection from one actual optional word

One real unpack instruction writes an existing product scratch cell. The
existing direct selector then reads its flag and word through structural
projections. No free optional-value projection or new instruction is added.
The same scratch cell can be overwritten for each chronological candidate.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Existing selector outputs and one writable product cell for the actual decoded candidate. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  selection : Direct.Refs ctx width
  unpacked : CWriteRef ctx (.product .bit (.unsignedWord width))

/-- These three actual destinations must be different storage identities. -/
structure Separation (refs : Refs ctx width) : Prop where
  acceptedNeSelected : refs.selection.accepted.key ≠ refs.selection.selected.key
  acceptedNeUnpacked : refs.selection.accepted.key ≠ refs.unpacked.key
  selectedNeUnpacked : refs.selection.selected.key ≠ refs.unpacked.key

/-- The eligibility bit is a projection of the existing unpacked product cell. -/
def eligible (refs : Refs ctx width) : CInputRef ctx .bit :=
  .first (Direct.writeInput refs.unpacked)

/-- The candidate word is a projection of that same actual product cell. -/
def candidate (refs : Refs ctx width) : CInputRef ctx (.unsignedWord width) :=
  .second (Direct.writeInput refs.unpacked)

/-- Actual unpacking charges the canonical nominal decoding instruction. -/
def unpackOp (input : CInputRef ctx (.option (.unsignedWord width))) (refs : Refs ctx width) :=
  ClassicalOp.unpackOption ctx input refs.unpacked

/-- One actual unpack precedes the existing stored-bit first-success control flow. -/
def into {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.option (.unsignedWord width))) (refs :
      Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (unpackOp input refs))
    (Direct.into (model := model) (eligible refs) (candidate refs) refs.selection)

/-- The real intermediate store supplies the direct selector's actual branch record. -/
def step {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.option (.unsignedWord width))) (refs :
      Refs ctx width)
    (store : Store ctx) : Store ctx × (into (model := model) input refs).Path :=
  let unpacked := BitWord.instructionStep (execution := model) (unpackOp input refs) store
  let selected := Direct.step (model := model) (eligible refs) (candidate refs) refs.selection
    unpacked.1
  (selected.1, (unpacked.2, selected.2))

/-- Exact whole-store execution preserves every quantum-reference block and caller history. -/
theorem into_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) input refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step (model := model) input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    Direct.into_execute, State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The native unpack gives exactly the structural eligibility and candidate values. -/
theorem unpack_reads (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (store : Store ctx) :
    (store.applyOp (unpackOp input refs)).read (eligible refs) =
        (CShape.unpackOption (store.read input)).first ∧
      (store.applyOp (unpackOp input refs)).read (candidate refs) =
        (CShape.unpackOption (store.read input)).second := by
  have actual := Store.read_applyOp_output store (unpackOp input refs)
  exact ⟨congrArg CShape.Value.first actual, congrArg CShape.Value.second actual⟩

/-- The direct selector consumes disjoint actual projections after the real unpack. -/
theorem directSeparation (refs : Refs ctx width) (separated : Separation refs) :
    Direct.Separation (eligible refs) (candidate refs) refs.selection := by
  refine ⟨?_, ?_, ?_, ?_, separated.acceptedNeSelected⟩
  all_goals
    simp only [eligible, candidate, Direct.writeInput, CInputRef.storageKeys,
      List.mem_singleton]
  · exact separated.acceptedNeUnpacked
  · exact separated.selectedNeUnpacked
  · exact separated.acceptedNeUnpacked
  · exact separated.selectedNeUnpacked

/-- Every structural caller read outside the three actual writes survives the entire step. -/
theorem into_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (acceptedFree : refs.selection.accepted.key ∉ other.storageKeys)
    (selectedFree : refs.selection.selected.key ∉ other.storageKeys)
    (unpackedFree : refs.unpacked.key ∉ other.storageKeys) :
    (step (model := model) input refs store).1.read other = store.read other :=
  (Direct.into_callerFrame (model := model) (eligible refs) (candidate refs) refs.selection
    (store.applyOp (unpackOp input refs)) other acceptedFree selectedFree).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (unpackOp input refs) other unpackedFree)

/-- A logical observation of the two actual selector cells, used only to state correctness. -/
def selectedValue (refs : Direct.Refs ctx width) (store : Store ctx) :
    (CShape.option (.unsignedWord width)).Value :=
  CShape.packOption (.product (store.read (Direct.writeInput refs.accepted))
    (store.read (Direct.writeInput refs.selected)))

/-- The mathematical ordered update keeps the earliest available candidate. -/
def retainValue (previous current : (CShape.option (.unsignedWord width)).Value) :
    (CShape.option (.unsignedWord width)).Value :=
  match previous with
  | .optionNone => current
  | .optionSome value => .optionSome value

private theorem bit_value (value : CShape.Value .bit) : value = .bit value.toBool := by
  cases value
  rfl

private theorem packed_update (oldFlag : CShape.Value .bit) (oldWord : CShape.Word width)
    (current : (CShape.option (.unsignedWord width)).Value) :
    CShape.packOption (.product
      (.bit (oldFlag.toBool || (CShape.unpackOption current).first.toBool))
      (if !oldFlag.toBool && (CShape.unpackOption current).first.toBool then
        (CShape.unpackOption current).second else oldWord)) =
      retainValue (CShape.packOption (.product oldFlag oldWord)) current := by
  cases oldFlag with
  | bit flag => cases flag <;> cases current <;> rfl

/-- Actual unpack and first-success selection realize the original chronological optional update. -/
theorem into_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (separated : Separation refs) (store : Store ctx) :
    selectedValue refs.selection (step (model := model) input refs store).1 =
      retainValue (selectedValue refs.selection store) (store.read input) := by
  have outcome := Direct.into_correct (model := model) (eligible refs) (candidate refs)
    refs.selection
    (directSeparation refs separated) (store.applyOp (unpackOp input refs))
  have unpacked := unpack_reads input refs store
  have oldAccepted :
      (store.applyOp (unpackOp input refs)).read (Direct.writeInput refs.selection.accepted) =
        store.read (Direct.writeInput refs.selection.accepted) :=
    Store.read_applyOp_of_not_mem_storageKeys store (unpackOp input refs) _ (by
      simpa only [unpackOp, ClassicalOp.outputRef_unpackOption, Direct.writeInput,
        CInputRef.storageKeys, List.mem_singleton] using separated.acceptedNeUnpacked.symm)
  have oldSelected :
      (store.applyOp (unpackOp input refs)).read (Direct.writeInput refs.selection.selected) =
        store.read (Direct.writeInput refs.selection.selected) :=
    Store.read_applyOp_of_not_mem_storageKeys store (unpackOp input refs) _ (by
      simpa only [unpackOp, ClassicalOp.outputRef_unpackOption, Direct.writeInput,
        CInputRef.storageKeys, List.mem_singleton] using separated.selectedNeUnpacked.symm)
  have accepted := outcome.accepted
  have selected := outcome.selected
  rw [oldAccepted, unpacked.1] at accepted
  rw [oldAccepted, oldSelected, unpacked.1, unpacked.2] at selected
  change ((step (model := model) input refs store).1.read (Direct.writeInput
    refs.selection.accepted)).toBool = _
    at accepted
  change (step (model := model) input refs store).1.read (Direct.writeInput
    refs.selection.selected) = _ at selected
  unfold selectedValue
  rw [bit_value ((step (model := model) input refs store).1.read (Direct.writeInput
    refs.selection.accepted))]
  rw [accepted, selected]
  exact packed_update _ _ _

/-- Independent native allowance pays for unpacking and both possible persistent writes. -/
def eventEnvelope (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : ResourcePool
  model :=
  ResourcePool.ofList
    (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.unpackOption width))) :: Direct.copyTrace (model := model) width)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual optional-candidate path meets the independent native decoding/copy allowance. -/
theorem into_pool_le (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (path : (into (model := model) input refs).Path) :
    (into (model := model) input refs).resourcePool path ≤ eventEnvelope model width := by
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (unpackOp input refs)).eventTrace path.1 ++
      (Direct.into (model := model) (eligible refs) (candidate refs) refs.selection).eventTrace
        path.2) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, ResourcePool.ofList_append]
  exact add_le_add le_rfl (Direct.into_pool_le (eligible refs) (candidate refs) refs.selection _)

/-- Decoding precedes at most the two dependent writes of the existing selector. -/
theorem into_depth_le (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (path : (into (model := model) input refs).Path) :
    (into (model := model) input refs).depth (fun _ => 1) path ≤ 3 :=
  Nat.add_le_add (Nat.le_refl 1)
    (Direct.into_depth_le (eligible refs) (candidate refs) refs.selection path.2)

/-- The complete actual path retains exactly the already present resident context. -/
theorem into_resident_le (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (path : (into (model := model) input refs).Path) :
    (into (model := model) input refs).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq (BitWord.instruction (execution := model) (unpackOp input
    refs))
    (Direct.into (model := model) (eligible refs) (candidate refs) refs.selection) path).le.trans ?_
  exact SpacePool.max_le (Circuit.peakResidentSpace_classical
      (BitWord.selectedApplication (execution := model) (unpackOp input refs)) path.1).le
    (Direct.into_resident_le (eligible refs) (candidate refs) refs.selection path.2)

/-- The same path charges the actual scratch and selector cells through their existing roles. -/
theorem into_auxiliary_le (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (path : (into (model := model) input refs).Path) :
    (into (model := model) input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (BitWord.instruction (execution := model) (unpackOp input
    refs))
    (Direct.into (model := model) (eligible refs) (candidate refs) refs.selection) path).le.trans ?_
  exact SpacePool.max_le (Circuit.peakAuxiliarySpace_classical
      (BitWord.selectedApplication (execution := model) (unpackOp input refs)) path.1).le
    (Direct.into_auxiliary_le (eligible refs) (candidate refs) refs.selection path.2)

/-- Actual unpack and selection jointly restore every borrowed value and external correlation. -/
theorem into_borrowedRestored (input : CInputRef ctx (.option (.unsignedWord width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) input refs).BorrowedRestored Reference state
      ((into (model := model) input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq (BitWord.instruction (execution := model) (unpackOp input refs))
    (Direct.into (model := model) (eligible refs) (candidate refs) refs.selection) state
    (Circuit.borrowedRestored_classical
      (BitWord.selectedApplication (execution := model) (unpackOp input refs)) state)
    (Direct.into_borrowedRestored (eligible refs) (candidate refs) refs.selection Reference
      ((BitWord.instruction (execution := model) (unpackOp input refs)).execute Reference
        state))

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct.Optional
