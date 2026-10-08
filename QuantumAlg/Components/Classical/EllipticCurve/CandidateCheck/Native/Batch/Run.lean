/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Execution
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Actual repeated recovery run and complete output state

The real recovery tail is the run's only code. Its complete output manifest
reads the actual retained optional result. Grouping by that value and the
original history preserves every quantum-reference block and agrees exactly
with reading the same result from the actual returned store. No point,
success, secret or initialization condition is required for this equation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The actual allocated recovery tail and complete manifest form one executable run. -/
def recoveryTailRun (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    AlgorithmRun model ctx (batchResultCtx ctx width scalarWidth)
      (.option (.unsignedWord scalarWidth)) where
  code := recoveryTail curve modulus samples base target
  output := Output.all (batchResultCtx ctx width scalarWidth)
    (.read (batchResultRead ctx width scalarWidth))

/-- Read precisely the actual final optional result from the complete returned store. -/
def recoveryTailOutput (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store ctx × model.HiddenState) :
    CShape.Value (.option (.unsignedWord scalarWidth)) :=
  (recoveryTailStore curve modulus samples base target before).read
    (batchResultRead ctx width scalarWidth)

/-- Group complete original blocks by their actual result and untouched prior history. -/
def recoveryTailOutputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)) × History)
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  state.mapClassical (fun entry =>
    (recoveryTailOutput curve modulus samples base target (entry.1, entry.2.1), entry.2.2))

/-- The run's final output state uses that same unchanged complete register. -/
def recoveryTailRunOutputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)))
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  state.mapClassical (recoveryTailOutput curve modulus samples base target)

/-- The actual complete tail's observed optional result and old history. -/
def recoveryTailObservedState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)) × History)
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  ((recoveryTail curve modulus samples base target).execute Reference state).mapClassical
    (fun entry => (entry.1.read (batchResultRead ctx width scalarWidth), entry.2.2.1))

/-- Read the run's final output from its own full returned state. -/
def recoveryTailRunReadoutState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)))
      (Register.prod (batchResultCtx ctx width scalarWidth).register Reference) :=
  ((recoveryTailRun curve modulus samples base target).finalState Reference state).mapClassical
    (recoveryTailRun curve modulus samples base target).output.eval

/-- Retain the initial store as mathematical history for the complete run. -/
def recoveryTailRunPreparedState (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    State ctx Reference (model.HiddenState × Store ctx) :=
  state.mapClassical (fun before => (before.1, (before.2, before.1)))

section

attribute [local irreducible] recoveryTailObservedState recoveryTailOutputState
  recoveryTailRunReadoutState recoveryTailRunOutputState

/-- Actual result reading and old-history retention preserve every complete reference block. -/
theorem recoveryTail_outputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    recoveryTailObservedState curve modulus samples base target Reference state =
      recoveryTailOutputState curve modulus samples base target Reference state := by
  unfold recoveryTailObservedState
  rw [recoveryTail_execute]
  have packed := packBatchResult_observeAfter ctx width scalarWidth
    (fun current => current.read (batchResultRead ctx width scalarWidth)) Reference
    ((recoveryBatch curve modulus samples base target).execute Reference state)
  unfold packBatchResultObservedAfter packBatchResultExpectedAfter at packed
  erw [packed]
  let readPacked : Store (persistentCtx ctx width scalarWidth) →
      CShape.Value (.option (.unsignedWord scalarWidth)) := fun current =>
    (packBatchResultStep ctx width scalarWidth current).1.read
      (batchResultRead ctx width scalarWidth)
  have observed := recoveryBatch_observe curve modulus samples base target
    readPacked Reference state
  have readEq (before : Store ctx × model.HiddenState) :
      recoveryTailOutput curve modulus samples base target before =
        readPacked (recoveryBatchStore curve modulus samples base target before) := rfl
  have outputEq :
      state.mapClassical (fun entry =>
        (recoveryTailOutput curve modulus samples base target (entry.1, entry.2.1),
          entry.2.2)) =
      state.mapClassical (fun entry =>
        (readPacked (recoveryBatchStore curve modulus samples base target
          (entry.1, entry.2.1)), entry.2.2)) := by
    apply ExecutionState.executionState_mapClassical_congr state
    funext entry
    exact congrArg (fun value => (value, entry.2.2))
      (readEq (entry.1, entry.2.1))
  unfold recoveryTailOutputState
  have combined := observed.trans outputEq.symm
  convert combined using 1

/-- The run's output read is the projection of its complete observed record. -/
private theorem recoveryTailRun_readoutProjection
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    recoveryTailRunReadoutState curve modulus samples base target Reference state =
      (recoveryTailObservedState curve modulus samples base target Reference
        (recoveryTailRunPreparedState Reference state)).mapClassical Prod.fst := by
  unfold recoveryTailRunReadoutState recoveryTailObservedState
  rw [AlgorithmRun.finalState_readout]
  change ((recoveryTail curve modulus samples base target).execute Reference
    (recoveryTailRunPreparedState Reference state)).mapClassical
      (fun entry => entry.1.read (batchResultRead ctx width scalarWidth)) =
    (((recoveryTail curve modulus samples base target).execute Reference
      (recoveryTailRunPreparedState Reference state)).mapClassical
      (fun entry => (entry.1.read (batchResultRead ctx width scalarWidth),
        entry.2.2.1))).mapClassical Prod.fst
  have composed := ExecutionState.executionState_mapClassical_comp_instances
    (middle := inferInstance) (last := inferInstance) (result := inferInstance)
    ((recoveryTail curve modulus samples base target).execute Reference
      (recoveryTailRunPreparedState Reference state))
    (fun entry => (entry.1.read (batchResultRead ctx width scalarWidth),
      entry.2.2.1)) Prod.fst
  convert composed.symm using 1
  all_goals exact ExecutionState.executionState_mapClassical_congr _ (by funext entry; rfl)

/-- Dropping the old-history coordinate recovers the original input observation. -/
private theorem recoveryTailRun_outputProjection
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    (recoveryTailOutputState curve modulus samples base target Reference
      (recoveryTailRunPreparedState Reference state)).mapClassical Prod.fst =
      recoveryTailRunOutputState curve modulus samples base target Reference state := by
  let prepared : State ctx Reference (model.HiddenState × Store ctx) :=
    recoveryTailRunPreparedState Reference state
  unfold recoveryTailOutputState recoveryTailRunOutputState
  have collapseHistory :
      (prepared.mapClassical (fun entry =>
        (recoveryTailOutput curve modulus samples base target
          (entry.1, entry.2.1), entry.2.2))).mapClassical Prod.fst =
      prepared.mapClassical (fun entry =>
        recoveryTailOutput curve modulus samples base target
          (entry.1, entry.2.1)) := by
    convert (ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance) prepared
      (fun entry => (recoveryTailOutput curve modulus samples base target
        (entry.1, entry.2.1), entry.2.2)) Prod.fst) using 1
    exact ExecutionState.executionState_mapClassical_congr prepared
      (by funext entry; rfl)
  have collapsePrepared :
      prepared.mapClassical (fun entry =>
        recoveryTailOutput curve modulus samples base target
          (entry.1, entry.2.1)) =
      state.mapClassical (recoveryTailOutput curve modulus samples base target) := by
    unfold prepared recoveryTailRunPreparedState
    convert (ExecutionState.executionState_mapClassical_comp_instances
      (result := inferInstance) state
      (fun before => (before.1, (before.2, before.1)))
      (fun entry => recoveryTailOutput curve modulus samples base target
        (entry.1, entry.2.1))) using 1
    exact ExecutionState.executionState_mapClassical_congr state
      (by funext entry; rfl)
  exact collapseHistory.trans collapsePrepared

/-- Reading the complete run output groups the same original full quantum-reference blocks. -/
theorem recoveryTailRun_outputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx × model.HiddenState)
      (Register.prod ctx.register Reference)) :
    recoveryTailRunReadoutState curve modulus samples base target Reference state =
      recoveryTailRunOutputState curve modulus samples base target Reference state := by
  calc
    _ = (recoveryTailObservedState curve modulus samples base target Reference
      (recoveryTailRunPreparedState Reference state)).mapClassical Prod.fst :=
        recoveryTailRun_readoutProjection curve modulus samples base target Reference state
    _ = (recoveryTailOutputState curve modulus samples base target Reference
      (recoveryTailRunPreparedState Reference state)).mapClassical Prod.fst :=
        congrArg (fun current => current.mapClassical Prod.fst)
          (recoveryTail_outputState curve modulus samples base target Reference
            (recoveryTailRunPreparedState Reference state))
    _ = _ := recoveryTailRun_outputProjection curve modulus samples base target Reference state

end

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
