/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Run
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect

/-!
# Actual recovery output probabilities

The run reads its own final optional cell. Its output distribution is exactly
the pushforward of the same original input blocks through the actual returned
store's output read. Arbitrary old histories and quantum references remain in
the complete-state and event-weight equations. Normalization is needed only
for the existing PMF interface, not for execution or event-weight correctness.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

private theorem eventWeight_of_mapped_eq {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    {R : Register} (left : ExecutionState A R) (right : ExecutionState B R)
    (readLeft : A → C) (readRight : B → C)
    (leftDecision rightDecision : DecidableEq C)
    (same : @ExecutionState.mapClassical A C _ _ R leftDecision left readLeft =
      @ExecutionState.mapClassical B C _ _ R rightDecision right readRight) (event : C → Bool) :
    left.effectWeight (fun entry => if event (readLeft entry) = true then
        Effect.one R else Effect.zero R) =
      right.effectWeight (fun entry => if event (readRight entry) = true then
        Effect.one R else Effect.zero R) := by
  have weighted := congrArg (fun output : ExecutionState C R => output.effectWeight
    (fun entry => if event entry = true then Effect.one R else Effect.zero R)) same
  simpa only [ExecutionState.effectWeight_mapClassical_decision] using weighted

/-- Every Boolean event has the same weight in the actual output and original complete blocks. -/
theorem recoveryTail_eventWeight (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (event : CShape.Value (.option (.unsignedWord scalarWidth)) → Bool) :
    ((recoveryTail curve modulus samples base target).execute Reference state).effectWeight
        (fun entry => if event (entry.1.read (batchResultRead ctx width scalarWidth)) = true then
          Effect.one (Register.prod (batchResultCtx ctx width scalarWidth).register Reference)
        else Effect.zero
          (Register.prod (batchResultCtx ctx width scalarWidth).register Reference)) =
      state.effectWeight (fun entry =>
        if event (recoveryTailOutput curve modulus samples base target entry.1) = true then
          Effect.one (Register.prod ctx.register Reference)
        else Effect.zero (Register.prod ctx.register Reference)) := by
  exact eventWeight_of_mapped_eq
    (C := CShape.Value (.option (.unsignedWord scalarWidth)) × History)
    ((recoveryTail curve modulus samples base target).execute Reference state)
    state
    (fun entry => (entry.1.read (batchResultRead ctx width scalarWidth), entry.2.1))
    (fun entry => (recoveryTailOutput curve modulus samples base target entry.1, entry.2))
    _ _
    (recoveryTail_outputState curve modulus samples base target Reference state)
    (fun entry => event entry.1)

/-- The actual output PMF uses the same incoming state and actual returned-store read. -/
theorem recoveryTailRun_outputDistribution (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    (initial : Input ctx Reference) :
    (recoveryTailRun curve modulus samples base target).outputDistribution initial =
      (initial.state.toPMF initial.normalized).map
        (recoveryTailOutput curve modulus samples base target) := by
  let run := recoveryTailRun curve modulus samples base target
  have readout := AlgorithmRun.finalState_readout run Reference initial.state
  have observed := recoveryTailRun_outputState curve modulus samples base target
    Reference initial.state
  have complete := readout.symm.trans observed
  apply PMF.ext
  intro value
  have actualProbability := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute Reference initial.state)
      (run.execute_normalized initial) run.result)
  have inputProbability := congrArg (fun distribution => distribution value)
    (ExecutionState.toPMF_mapClassical initial.state initial.normalized
      (recoveryTailOutput curve modulus samples base target))
  have masses := congrArg (fun output :
      ExecutionState (CShape.Value (.option (.unsignedWord scalarWidth)))
        (Register.prod ctx.register Reference) => ENNReal.ofReal (output.block value).mass) complete
  exact actualProbability.symm.trans (masses.trans inputProbability)

/-- Every actual Boolean output event is the same event on the original input blocks. -/
theorem recoveryTailRun_eventProbability (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    (initial : Input ctx Reference)
    (event : CShape.Value (.option (.unsignedWord scalarWidth)) → Bool) :
    ((recoveryTailRun curve modulus samples base target).outputDistribution initial).map
        event true =
      (initial.state.toPMF initial.normalized).map
        (event ∘ recoveryTailOutput curve modulus samples base target) true := by
  rw [recoveryTailRun_outputDistribution, PMF.map_comp]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
