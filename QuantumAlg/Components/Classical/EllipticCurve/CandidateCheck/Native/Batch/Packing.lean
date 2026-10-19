/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.State.History

/-!
# Actual final batch-result packing

After all original attempts, one actual retained cell is allocated. The
original option-pack instruction reads the persistent accepted and selected
latches and writes that cell. Its real record preserves all earlier inputs,
the seven persistent destinations, arbitrary quantum references and history.
The final native event and the new optional word are both charged explicitly.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  (ctx : RuntimeCtx model.kind) (width scalarWidth : Nat)

/-- The actual retention and option-pack return their complete Store and instruction path. -/
def packBatchResultStep (before : Store (persistentCtx ctx width scalarWidth)) :
    Store (batchResultCtx ctx width scalarWidth) × (packBatchResult ctx width scalarWidth).Path :=
  let inner := persistentCtx ctx width scalarWidth
  let entered := before.pushRetained inner.canonicalFreshKey
    (.option (.unsignedWord scalarWidth)) inner.canonicalFreshKey_fresh
  let finished := BitWord.instructionStep (execution := model)
    (batchResultOp ctx width scalarWidth) entered
  (finished.1, ((), finished.2))

/-- Keep the service state beside the actual final packing step. -/
def packBatchResultRecordStep
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    (Store (batchResultCtx ctx width scalarWidth) × model.HiddenState) ×
      (packBatchResult ctx width scalarWidth).Path :=
  let packed := packBatchResultStep ctx width scalarWidth before.1
  ((packed.1, before.2), packed.2)

section

attribute [local irreducible] persistentCtx

/-- Lift the actual deterministic Store record to every complete quantum-reference block. -/
@[irreducible] def packBatchResultState (Reference : Register) {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    State (batchResultCtx ctx width scalarWidth) Reference
      (model.HiddenState × (History × (packBatchResult ctx width scalarWidth).Path)) :=
  state.mapClassical (fun entry =>
    let result := packBatchResultRecordStep ctx width scalarWidth (entry.1, entry.2.1)
    (result.1.1, (result.1.2, (entry.2.2, result.2))))

end

section

attribute [local irreducible] persistentCtx

/-- Actual result retention and packing preserve every complete reference block and history. -/
lemma packBatchResult_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    (packBatchResult ctx width scalarWidth).execute environment Reference state =
      packBatchResultState ctx width scalarWidth Reference state := by
  unfold packBatchResult
  erw [Circuit.execute_seq]
  erw [Circuit.execute_retain]
  erw [BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory]
  erw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  erw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  unfold packBatchResultState
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Reading the packed store and old history preserves every complete reference block. -/
def packBatchResultObserved {D History : Type}
    [Fintype D] [Fintype History]
    (observe : Store (batchResultCtx ctx width scalarWidth) × History → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    ExecutionState D (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  (packBatchResultState ctx width scalarWidth Reference state).mapClassical
    (fun entry => observe (entry.1, entry.2.2.1))

/-- The same observation computed from the actual final store record. -/
def packBatchResultExpected {D History : Type}
    [Fintype D] [Fintype History]
    (observe : Store (batchResultCtx ctx width scalarWidth) × History → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    ExecutionState D (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  state.mapClassical (fun entry =>
    observe ((packBatchResultStep ctx width scalarWidth entry.1).1, entry.2.2))

/-- The packed store and old history give the same observation. -/
lemma packBatchResult_observe {D History : Type}
    [Fintype D] [Fintype History]
    (observe : Store (batchResultCtx ctx width scalarWidth) × History → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × History)) :
    packBatchResultObserved ctx width scalarWidth observe Reference state =
      packBatchResultExpected ctx width scalarWidth observe Reference state := by
  unfold packBatchResultObserved packBatchResultExpected
  unfold packBatchResultState
  exact (ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance) state _ _).trans
      (ExecutionState.executionState_mapClassical_congr state rfl)

/-- Observe the original history after final packing and path reassociation. -/
def packBatchResultObservedAfter {D H Prefix : Type}
    [Fintype D] [Fintype H] [Fintype Prefix]
    (observe : Store (batchResultCtx ctx width scalarWidth) → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (H × Prefix))) :
    ExecutionState (D × H)
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  ((packBatchResultState ctx width scalarWidth Reference state).mapHistory
    (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))).mapClassical
      (fun entry => (observe entry.1, entry.2.2.1))

/-- Observe the same history directly from the actual final packing record. -/
def packBatchResultExpectedAfter {D H Prefix : Type}
    [Fintype D] [Fintype H] [Fintype Prefix]
    (observe : Store (batchResultCtx ctx width scalarWidth) → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (H × Prefix))) :
    ExecutionState (D × H)
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  state.mapClassical (fun entry =>
    (observe (packBatchResultStep ctx width scalarWidth entry.1).1, entry.2.2.1))

/-- Final packing and path reassociation leave the original history observable. -/
lemma packBatchResult_observeAfter {D H Prefix : Type}
    [Fintype D] [Fintype H] [Fintype Prefix]
    (observe : Store (batchResultCtx ctx width scalarWidth) → D)
    (Reference : Register)
    (state : State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (H × Prefix))) :
    packBatchResultObservedAfter ctx width scalarWidth observe Reference state =
      packBatchResultExpectedAfter ctx width scalarWidth observe Reference state := by
  unfold packBatchResultObservedAfter packBatchResultExpectedAfter
  simp only [State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  convert (packBatchResult_observe ctx width scalarWidth
    (fun current => (observe current.1, current.2.1)) Reference state) using 1
  · exact ExecutionState.executionState_mapClassical_congr _ (by funext entry; rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ (by funext entry; rfl)

end

/-- Packing after any preceding circuit reads its actual returned persistent store. -/
lemma packBatchResult_after {pre : RuntimeCtx model.kind}
    (first : Circuit model pre (persistentCtx ctx width scalarWidth))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    (first.seq (packBatchResult ctx width scalarWidth)).execute environment Reference state =
      (packBatchResultState ctx width scalarWidth Reference
        (first.execute environment Reference state)).mapHistory
          (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) := by
  rw [Circuit.execute_seq, packBatchResult_execute]

/-- The actual final output encodes exactly the incoming persistent first-success latches. -/
lemma packBatchResultStep_output (before : Store (persistentCtx ctx width scalarWidth)) :
    (packBatchResultStep ctx width scalarWidth before).1.read
      (batchResultRead ctx width scalarWidth) =
        CShape.packOption (.product
          (before.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
          (before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))) := by
  let inner := persistentCtx ctx width scalarWidth
  let shape := CShape.option (.unsignedWord scalarWidth)
  let entered := before.pushRetained inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh
  have actual := Store.read_applyOp_output entered (batchResultOp ctx width scalarWidth)
  change (packBatchResultStep ctx width scalarWidth before).1.read
    (batchResultRead ctx width scalarWidth) =
      CShape.packOption (.product
        (entered.read ((CInputRef.storage
          (persistentAccepted ctx width scalarWidth).toCStorageRef).underRetained
            inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh))
        (entered.read ((CInputRef.storage
          (persistentSelected ctx width scalarWidth).toCStorageRef).underRetained
            inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh))) at actual
  simpa only [entered, Store.read_pushRetained_underRetained] using actual

/-- Every earlier structural input and retained latch survives the new output write unchanged. -/
lemma packBatchResultStep_read_other (before : Store (persistentCtx ctx width scalarWidth))
    {shape : CShape} (input : CInputRef (persistentCtx ctx width scalarWidth) shape) :
    (packBatchResultStep ctx width scalarWidth before).1.read
      (input.underRetained (persistentCtx ctx width scalarWidth).canonicalFreshKey
        (.option (.unsignedWord scalarWidth))
        (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh) = before.read input := by
  let inner := persistentCtx ctx width scalarWidth
  let outputShape := CShape.option (.unsignedWord scalarWidth)
  let entered := before.pushRetained inner.canonicalFreshKey outputShape
    inner.canonicalFreshKey_fresh
  exact (Store.read_applyOp_of_not_mem_storageKeys entered (batchResultOp ctx width scalarWidth)
    (input.underRetained inner.canonicalFreshKey outputShape inner.canonicalFreshKey_fresh)
    (input.fresh_not_mem_storageKeys_underRetained inner.canonicalFreshKey outputShape
      inner.canonicalFreshKey_fresh)).trans
      (Store.read_pushRetained_underRetained before inner.canonicalFreshKey outputShape
        inner.canonicalFreshKey_fresh input)

/-- The final retained result emits exactly the original paid option-pack instruction. -/
lemma packBatchResult_eventTrace (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packOption scalarWidth)))] := by
  change (BitWord.instruction (execution := model)
    (batchResultOp ctx width scalarWidth)).eventTrace path.2 = _
  exact BitWord.bitWord_instruction_eventTrace _ path.2

/-- The exact native pool is the singleton event of that same actual final instruction. -/
lemma packBatchResult_resourcePool (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).resourcePool path =
      ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packOption scalarWidth)))] :=
  congrArg ResourcePool.ofList (packBatchResult_eventTrace ctx width scalarWidth path)

/-- Exactly one real native instruction executes even for a zero-width selected word. -/
lemma packBatchResult_eventCount (path : (packBatchResult ctx width scalarWidth).Path) :
    ((packBatchResult ctx width scalarWidth).eventTrace path).length = 1 := rfl

/-- The actual final dependency duration is exactly the original pack-operation duration. -/
lemma packBatchResult_depth (duration : Resource.Event model → Nat)
    (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).depth duration path =
      duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.nominalEncoding (.packOption scalarWidth)))) := by
  change 0 + (BitWord.instruction (execution := model)
    (batchResultOp ctx width scalarWidth)).depth duration path.2 = _
  exact (congrArg (fun value => 0 + value)
    (BitWord.bitWord_instruction_depth
      (execution := model) (batchResultOp ctx width scalarWidth) duration path.2)).trans
        (Nat.zero_add _)

/-- Resident peak adds the actual final optional word beside all seven persistent destinations. -/
lemma packBatchResult_resident (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).peakResidentSpace path =
      SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  exact (Circuit.retainedStep_peakResidentSpace (persistentCtx ctx width scalarWidth)
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (BitWord.selectedApplication (execution := model)
      (batchResultOp ctx width scalarWidth)) path).trans
      (RuntimeCtx.residentSpace_addRetained _ _ _ _)

/-- Auxiliary peak includes the same real output allocation and the complete prior workspace. -/
lemma packBatchResult_auxiliary (path : (packBatchResult ctx width scalarWidth).Path) :
    (packBatchResult ctx width scalarWidth).peakAuxiliarySpace path =
      SpacePool.ofShape (.option (.unsignedWord scalarWidth)) +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  exact (Circuit.retainedStep_peakAuxiliarySpace (persistentCtx ctx width scalarWidth)
    (persistentCtx ctx width scalarWidth).canonicalFreshKey (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (BitWord.selectedApplication (execution := model)
      (batchResultOp ctx width scalarWidth)) path).trans
      (RuntimeCtx.auxiliarySpace_addRetained _ _ _ _)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
