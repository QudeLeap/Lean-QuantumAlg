/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Semantics

/-!
# Complete actual persistent recovery execution

Actual seven-cell allocation supplies the initial store of the chronological
attempt loop. Actual final retention and option packing then read the loop's
returned latches. These complete execution equations retain every quantum
reference block, original history and real path of all three stages.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The allocated store and unchanged service state enter the actual ordered loop. -/
def recoveryBatchState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) × model.HiddenState :=
  repeatedAttemptsState (environment := environment) curve modulus samples base target
    (persistentInitialStore width scalarWidth before.1, before.2)

/-- The actual allocated initial store feeds the original ordered attempt updates. -/
def recoveryBatchStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) :=
  (recoveryBatchState (environment := environment) curve modulus samples base target before).1

/-- Actual optional-result retention and packing consume the real loop's returned store. -/
def recoveryTailStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    Store (batchResultCtx ctx width scalarWidth) :=
  (packBatchResultStep ctx width scalarWidth
    (recoveryBatchStore (environment := environment) curve modulus samples base target before)).1

/-- Map the actual complete recovery batch record over all incoming reference blocks. -/
def recoveryBatchRecordState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (record : Store ctx × model.HiddenState →
      (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
        (recoveryBatch curve modulus samples base target).Path)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    State (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (History × (recoveryBatch curve modulus samples base target).Path)) :=
  state.mapClassical (fun entry =>
    let result := record (entry.1, entry.2.1)
    (result.1.1, (result.1.2, (entry.2.2, result.2))))

omit [BitWord.Selected model] in
private lemma deterministicTail_after {pre middle : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle middle)
    (record : Store middle × model.HiddenState →
      (Store middle × model.HiddenState) × second.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State middle Reference (model.HiddenState × History)),
      second.execute environment Reference state = state.mapClassical (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State pre Reference (model.HiddenState × History)) :
    (first.seq second).execute environment Reference state =
      (first.execute environment Reference state).mapClassical (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2.1, (entry.2.2.2, result.2))))) := by
  rw [Circuit.execute_seq, equation]
  simp only [State.mapHistory]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual allocator and complete loop preserve the entire incoming reference and history. -/
lemma recoveryBatch_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    ∃ record : Store ctx × model.HiddenState →
        (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
          (recoveryBatch curve modulus samples base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (recoveryBatch curve modulus samples base target).execute environment Reference state =
          recoveryBatchRecordState curve modulus samples base target record Reference state) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        recoveryBatchStore (environment := environment) curve modulus samples base target before
          := by
  obtain ⟨loopRecord, loopEquation, loopStore⟩ :=
    repeatedAttempts_actualRecord (environment := environment) curve modulus samples base target
  let record : Store ctx × model.HiddenState →
      (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
        (recoveryBatch curve modulus samples base target).Path := fun before =>
    let allocated := persistentAllocationStep width scalarWidth before.1
    let looped := loopRecord (allocated.1, before.2)
    (looped.1, (allocated.2, looped.2))
  refine ⟨record, ?_, ?_⟩
  · intro Reference History _ state
    have whole := deterministicTail_after (retainPersistent ctx width scalarWidth)
      (repeatedAttempts curve modulus samples base target) loopRecord loopEquation Reference state
    rw [retainPersistent_execute] at whole
    unfold persistentAllocationState at whole
    erw [ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance)] at whole
    unfold recoveryBatchRecordState
    exact whole.trans (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro before
    exact loopStore (persistentInitialStore width scalarWidth before.1, before.2)

/-- Observing the actual loop's returned store preserves every incoming reference and history. -/
lemma recoveryBatch_observe {D : Type} [Fintype D]
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (observe : Store (persistentCtx ctx width scalarWidth) → D)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((recoveryBatch curve modulus samples base target).execute environment Reference
      state).mapClassical
      (fun entry => (observe entry.1, entry.2.2.1)) =
        state.mapClassical (fun entry =>
          (observe (recoveryBatchStore (environment := environment) curve modulus samples base
            target
            (entry.1, entry.2.1)), entry.2.2)) := by
  obtain ⟨record, equation, returned⟩ :=
    recoveryBatch_actualRecord (environment := environment) curve modulus samples base target
  rw [equation Reference state]
  unfold recoveryBatchRecordState
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance)]
  apply ExecutionState.executionState_mapClassical_congr state
  funext entry
  simp only [Function.comp_def, returned]

/-- Use the proved allocated-loop record as the input to final packing. -/
noncomputable def recoveryBatchRecord (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Store ctx × model.HiddenState →
      (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
        (recoveryBatch curve modulus samples base target).Path :=
  Classical.choose (recoveryBatch_actualRecord (environment := environment) curve modulus
    samples base target)

/-- Follow the proved allocated-loop record with the actual final packing execution. -/
def recoveryTailComposedState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    State (batchResultCtx ctx width scalarWidth) Reference
      (model.HiddenState × (History × (recoveryTail curve modulus samples base target).Path)) :=
  (packBatchResultState ctx width scalarWidth Reference
    (recoveryBatchRecordState curve modulus samples base target
      (recoveryBatchRecord (environment := environment) curve modulus samples base target)
        Reference state)).mapHistory
      (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))

/-- One named record follows the actual allocated loop with its final output instruction. -/
def recoveryTailRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Store ctx × model.HiddenState →
      (Store (batchResultCtx ctx width scalarWidth) × model.HiddenState) ×
        (recoveryTail curve modulus samples base target).Path := fun before =>
  let looped := recoveryBatchRecord (environment := environment) curve modulus samples base
    target before
  let packed := packBatchResultStep ctx width scalarWidth looped.1.1
  ((packed.1, looped.1.2), (looped.2, packed.2))

/-- The actual tail first executes the allocated loop, then retains and packs its result. -/
lemma recoveryTail_execute (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (recoveryTail curve modulus samples base target).execute environment Reference state =
      (packBatchResultState ctx width scalarWidth Reference
        ((recoveryBatch curve modulus samples base target).execute environment Reference
          state)).mapHistory
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))) :=
  packBatchResult_after ctx width scalarWidth
    (recoveryBatch curve modulus samples base target) Reference state

/-- The final actual store is the result of the same named complete record. -/
lemma recoveryTailRecord_store (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    (recoveryTailRecord (environment := environment) curve modulus samples base target before).1.1 =
      recoveryTailStore (environment := environment) curve modulus samples base target before := by
  exact congrArg (fun current => (packBatchResultStep ctx width scalarWidth current).1)
    ((Classical.choose_spec
      (recoveryBatch_actualRecord (environment := environment) curve modulus samples base
        target)).2 before)

/-- One complete record accounts for the allocated loop, option packing, and service state. -/
lemma recoveryTail_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (recoveryTail curve modulus samples base target).execute environment Reference state =
      recoveryTailComposedState (environment := environment) curve modulus samples base target
        Reference state := by
  unfold recoveryTailComposedState
  exact (recoveryTail_execute curve modulus samples base target Reference state).trans
    (congrArg (fun (current :
        State (persistentCtx ctx width scalarWidth) Reference
          (model.HiddenState × (History ×
            (recoveryBatch curve modulus samples base target).Path))) =>
      (packBatchResultState ctx width scalarWidth Reference current).mapHistory
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))))
      ((Classical.choose_spec
        (recoveryBatch_actualRecord (environment := environment) curve modulus samples base
          target)).1 Reference state))

/-- The complete actual tail returns the option encoded by its final persistent latches. -/
lemma recoveryTailStore_output (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    (recoveryTailStore (environment := environment) curve modulus samples base target before).read
      (batchResultRead ctx width scalarWidth) =
        CShape.packOption (.product
          ((recoveryBatchStore (environment := environment) curve modulus samples base target
            before).read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef))
          ((recoveryBatchStore (environment := environment) curve modulus samples base target
            before).read
            (.storage (persistentSelected ctx width scalarWidth).toCStorageRef))) :=
  packBatchResultStep_output ctx width scalarWidth
    (recoveryBatchStore (environment := environment) curve modulus samples base target before)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
