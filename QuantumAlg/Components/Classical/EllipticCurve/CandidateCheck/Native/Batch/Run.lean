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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

/-- The actual allocated recovery tail and complete manifest form one executable run. -/
def recoveryTailRun (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    AlgorithmRun ctx (batchResultCtx ctx width scalarWidth)
      (.option (.unsignedWord scalarWidth)) where
  code := recoveryTail curve modulus samples base target
  output := Output.all (batchResultCtx ctx width scalarWidth)
    (.read (batchResultRead ctx width scalarWidth))

/-- Read precisely the actual final optional result from the complete returned store. -/
def recoveryTailOutput (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx) :
    CShape.Value (.option (.unsignedWord scalarWidth)) :=
  (recoveryTailStore curve modulus samples base target before).read
    (batchResultRead ctx width scalarWidth)

/-- Group complete original blocks by their actual result and untouched prior history. -/
def recoveryTailOutputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)) × History)
      (Register.prod ctx.register Reference) :=
  state.mapClassical (fun entry =>
    (recoveryTailOutput curve modulus samples base target entry.1, entry.2))

/-- Actual result reading and old-history retention preserve every complete reference block. -/
theorem recoveryTail_outputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    ((recoveryTail curve modulus samples base target).execute Reference state).mapClassical
        (fun entry => (entry.1.read (batchResultRead ctx width scalarWidth), entry.2.1)) =
      recoveryTailOutputState curve modulus samples base target Reference state := by
  obtain ⟨record, equation, returned⟩ :=
    recoveryTail_actualRecord curve modulus samples base target
  conv =>
    lhs
    arg 1
    rw [equation Reference state]
    unfold recoveryTailRecordState
  conv =>
    lhs
    erw [persistentTwoMaps_eq _ _ (Classical.decEq _) state _ _]
  conv =>
    lhs
    arg 2
    simp only [Function.comp_def, returned]
  unfold recoveryTailOutputState recoveryTailOutput
  exact (Circuit.mapClassical_canonicalDecision _ state _).symm

/-- Reading the complete run output groups the same original full quantum-reference blocks. -/
theorem recoveryTailRun_outputState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    (state : ExecutionState (Store ctx) (Register.prod ctx.register Reference)) :
    ((recoveryTailRun curve modulus samples base target).finalState Reference state).mapClassical
        (recoveryTailRun curve modulus samples base target).output.eval =
      state.mapClassical (recoveryTailOutput curve modulus samples base target) := by
  rw [AlgorithmRun.finalState_readout]
  obtain ⟨record, equation, returned⟩ :=
    recoveryTail_actualRecord curve modulus samples base target
  change ((recoveryTail curve modulus samples base target).execute Reference
    (state.mapClassical (fun store => (store, store)))).mapClassical
      (fun entry => entry.1.read (batchResultRead ctx width scalarWidth)) = _
  conv =>
    lhs
    arg 1
    rw [equation]
    unfold recoveryTailRecordState
  conv =>
    lhs
    erw [persistentTwoMaps_eq _ _ (Classical.decEq _)
      (state.mapClassical (fun store => (store, store))) _ _]
  conv =>
    lhs
    erw [persistentTwoMaps_eq _ _ (Classical.decEq _) state _ _]
  conv =>
    lhs
    arg 2
    simp only [Function.comp_def, returned]
  exact (Circuit.mapClassical_canonicalDecision _ state _).symm

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
