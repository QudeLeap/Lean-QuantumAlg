/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect.Store
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Input.Successor.Distribution
import all QuantumAlg.Core.Execution.Input.Successor.Sequence

/-!
# Actual output laws after an executed prefix

Projecting mathematical histories at a real circuit boundary preserves the
output law of its continuation. The live store, persistent service and full
quantum-reference correlations remain those of the original execution.
-/

namespace QuantumAlg.AlgorithmRun

variable {allowAllocation : Bool}

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre middle post : RuntimeCtx model.kind} {shape : CShape}

private lemma observedDistribution_apply {C D : Type} [Fintype C] [Finite D]
    {R : Register} (state : ExecutionState C R) (normalized : state.IsNormalized)
    (read : C → D) (value : D) :
    (state.toPMF normalized).map read value =
      ENNReal.ofReal (state.effectWeight (fun record =>
        if read record = value then Effect.one R else Effect.zero R)) := by
  let := Fintype.ofFinite D
  have mapped := congrArg (fun distribution : PMF D => distribution value)
    (ExecutionState.toPMF_mapClassical state normalized read)
  exact mapped.symm.trans (congrArg ENNReal.ofReal
    (ExecutionState.effectWeight_observed_mass state read value).symm)

/-- The actual output distribution equals the readout of its real successor
input; only unobservable initial-store and path histories are grouped. -/
lemma outputDistribution_eq_nextInput_readout
    (run : AlgorithmRun model pre post shape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    run.outputDistribution environment input =
      (((run.code.nextInput environment input).state.toPMF
        (run.code.nextInput environment input).normalized).map
          (fun record => run.output.eval record.1)) := by
  rw [Circuit.nextInput_readoutDistribution]
  apply PMF.ext
  intro value
  rw [outputDistribution_apply_eq_effectWeight]
  erw [observedDistribution_apply]
  convert congrArg ENNReal.ofReal (storedEffectWeight_eq_code_skip run environment input
    (fun store => if run.output.eval store = value then
      Effect.one (post.register.prod Reference) else Effect.zero (post.register.prod Reference)))
    using 1
  · apply congrArg ENNReal.ofReal
    apply congrArg ((run.execute environment Reference input.state).effectWeight)
    funext record
    rw [AlgorithmRun.result]
  · apply congrArg ENNReal.ofReal
    apply congrArg₂ (fun
      (state : State post Reference (model.HiddenState × (Unit × run.code.Path)))
      (effects : Store post × (model.HiddenState × (Unit × run.code.Path)) →
        Effect (post.register.prod Reference)) => state.effectWeight effects)
    · apply congrArg (run.code.execute environment Reference)
      dsimp only [State.skip, State.mapHistory]
      exact ExecutionState.executionState_mapClassical_congr_decision input.state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry => (entry.1, (entry.2, ()))) (fun _ => rfl) _ _
    · funext record
      split_ifs <;> rfl

/-- An executed prefix followed by the actual continuation has exactly the
continuation's output law on the prefix's real, history-projected input. -/
lemma outputDistribution_after_prefix (first : Circuit model pre middle allowAllocation)
    (continuation : AlgorithmRun model middle post shape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    ({ code := first.seq continuation.code, output := continuation.output } :
      AlgorithmRun model pre post shape allowAllocation).outputDistribution environment input =
        continuation.outputDistribution environment (first.nextInput environment input) := by
  rw [outputDistribution_eq_nextInput_readout,
    outputDistribution_eq_nextInput_readout, Circuit.nextInput_seq]

/-- Forgetting the retained initial store gives precisely the actual output
distribution, with no independence assumption on that initial store. -/
lemma relationalDistribution_map_output
    (run : AlgorithmRun model pre post shape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) :
    (run.relationalDistribution environment input).map Prod.snd =
      run.outputDistribution environment input := by
  simp only [relationalDistribution, outputDistribution, PMF.map_comp, Function.comp_def]

/-- A continuation's relational success floor transfers through its actual
prefix when its accepted pairs imply the independently prescribed output.
No initial-store independence or fresh service state is assumed. -/
lemma relationalSuccess_after_prefix (first : Circuit model pre middle allowAllocation)
    (continuation : AlgorithmRun model middle post shape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference)
    (acceptedPairs : Set (Store middle × CShape.Value shape))
    (acceptedOutputs : Set (CShape.Value shape)) (floor : ENNReal)
    (lower : floor ≤ (continuation.relationalDistribution environment
      (first.nextInput environment input)).toOuterMeasure acceptedPairs)
    (inclusion : acceptedPairs ⊆ Prod.snd ⁻¹' acceptedOutputs) :
    floor ≤ (({ code := first.seq continuation.code, output := continuation.output } :
      AlgorithmRun model pre post shape
        allowAllocation).relationalDistribution environment input).toOuterMeasure
        (Prod.snd ⁻¹' acceptedOutputs) := by
  have projection := PMF.toOuterMeasure_map_apply Prod.snd
    (continuation.relationalDistribution environment
      (first.nextInput environment input)) acceptedOutputs
  rw [relationalDistribution_map_output] at projection
  have lowerOutput := (lower.trans
    ((continuation.relationalDistribution environment
      (first.nextInput environment input)).toOuterMeasure.mono
      inclusion)).trans_eq projection.symm
  have prefixProjection := congrArg
    (fun distribution : PMF (CShape.Value shape) => distribution.toOuterMeasure acceptedOutputs)
    (outputDistribution_after_prefix first continuation environment input)
  have lowerPrefixed := lowerOutput.trans_eq prefixProjection.symm
  have wholeProjection := PMF.toOuterMeasure_map_apply Prod.snd
    (({ code := first.seq continuation.code, output := continuation.output } :
      AlgorithmRun model pre post shape
        allowAllocation).relationalDistribution environment input) acceptedOutputs
  rw [relationalDistribution_map_output] at wholeProjection
  exact lowerPrefixed.trans_eq wholeProjection

end

end QuantumAlg.AlgorithmRun
