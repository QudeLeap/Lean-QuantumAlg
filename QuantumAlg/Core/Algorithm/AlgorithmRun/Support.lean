/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Core.Execution.Circuit.Support
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Actual algorithm event comparison on a coherent good input

Two actual runs start from the same complete caller and persistent-service input, with a normalized
complete quantum-reference vector. Agreement concerns their complete event weights on
the same subnormalized good density, including every coherent cross term.
Their true output probabilities then differ by at most four times the omitted
vector norm. The real Output and retained initial Store determine each event.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {outputShape : CShape}

/-- A definite caller and explicit service state supply one normalized pure quantum input. -/
def pureInput {Reference : Register} (stored : Execution.Store pre × model.HiddenState)
    (vector : NormalizedVector (Register.prod pre.register Reference)) :
    Execution.OracleInput model.classicalOracles pre Reference where
  state := ExecutionState.ofValue stored (DensityOperator.ofPure vector)
  normalized := (ExecutionState.ofValue_mass stored (DensityOperator.ofPure vector)).trans
    (DensityOperator.ofPure_normalized vector)

/-- An event is tested against each complete actual execution record. -/
def recordEventEffects (run : AlgorithmRun model pre post outputShape) (Reference : Register)
    (event : run.Record → Bool) : run.Record → Effect (Register.prod post.register Reference) :=
  fun record => if event record = true then Effect.one (Register.prod post.register Reference)
    else Effect.zero (Register.prod post.register Reference)

private theorem execution_event_eq_pure_effectWeight
    (run : AlgorithmRun model pre post outputShape) {Reference : Register}
    (stored : Execution.Store pre × model.HiddenState)
    (vector : NormalizedVector (Register.prod pre.register Reference))
    (event : run.Record → Bool) :
    (run.executionDistribution (pureInput (model := model) stored vector)).map event true =
      ENNReal.ofReal ((run.effectPullback Reference
        (run.recordEventEffects Reference event) stored).weight
          (DensityOperator.ofPure vector)) := by
  rw [executionDistribution_map_eq_input_effectWeight]
  simp only [pureInput, ExecutionState.effectWeight_ofValue_decision]
  rfl

variable {actualPost idealPost : RuntimeCtx model.kind} {actualShape idealShape : CShape}

/-- Coherent good-density agreement bounds the true event probabilities of two actual runs. -/
theorem execution_event_le_add_four_mul_omitted_norm
    (actual : AlgorithmRun model pre actualPost actualShape)
    (ideal : AlgorithmRun model pre idealPost idealShape) {Reference : Register}
    (stored : Execution.Store pre × model.HiddenState)
    (vector : NormalizedVector (Register.prod pre.register Reference))
    (good : HilbertVector (Register.prod pre.register Reference)) (bounded : ‖good‖ ≤ 1)
    (actualEvent : actual.Record → Bool) (idealEvent : ideal.Record → Bool)
    (goodAgreement :
      (actual.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (actual.recordEventEffects Reference actualEvent) =
      (ideal.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (ideal.recordEventEffects Reference idealEvent)) :
    (ideal.executionDistribution (pureInput (model := model) stored vector)).map idealEvent true ≤
      (actual.executionDistribution (pureInput (model := model) stored vector)).map
          actualEvent true +
        ENNReal.ofReal (4 * ‖vector.vec - good‖) := by
  have actualGood := actual.effectWeight_execute Reference
    (ExecutionState.ofValue stored (DensityOperator.ofSubnormalizedVector good bounded))
    (actual.recordEventEffects Reference actualEvent)
  have idealGood := ideal.effectWeight_execute Reference
    (ExecutionState.ofValue stored (DensityOperator.ofSubnormalizedVector good bounded))
    (ideal.recordEventEffects Reference idealEvent)
  simp only [ExecutionState.effectWeight_ofValue_decision] at actualGood idealGood
  have comparison := Effect.weight_le_add_four_mul_omitted_norm
    (actual.effectPullback Reference (actual.recordEventEffects Reference actualEvent) stored)
    (ideal.effectPullback Reference (ideal.recordEventEffects Reference idealEvent) stored)
    vector good bounded (actualGood.symm.trans (goodAgreement.trans idealGood))
  rw [execution_event_eq_pure_effectWeight, execution_event_eq_pure_effectWeight]
  exact (ENNReal.ofReal_le_ofReal comparison).trans ENNReal.ofReal_add_le

/-- The same four-times-omitted-norm bound applies directly to real shaped output events. -/
theorem output_event_le_add_four_mul_omitted_norm
    (actual : AlgorithmRun model pre actualPost actualShape)
    (ideal : AlgorithmRun model pre idealPost idealShape) {Reference : Register}
    (stored : Execution.Store pre × model.HiddenState)
    (vector : NormalizedVector (Register.prod pre.register Reference))
    (good : HilbertVector (Register.prod pre.register Reference)) (bounded : ‖good‖ ≤ 1)
    (actualEvent : actualShape.Value → Bool) (idealEvent : idealShape.Value → Bool)
    (goodAgreement :
      (actual.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (actual.recordEventEffects Reference (actualEvent ∘ actual.result)) =
      (ideal.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (ideal.recordEventEffects Reference (idealEvent ∘ ideal.result))) :
    (ideal.outputDistribution (pureInput (model := model) stored vector)).map idealEvent true ≤
      (actual.outputDistribution (pureInput (model := model) stored vector)).map
          actualEvent true +
        ENNReal.ofReal (4 * ‖vector.vec - good‖) := by
  rw [outputDistribution, outputDistribution, PMF.map_comp, PMF.map_comp]
  exact execution_event_le_add_four_mul_omitted_norm actual ideal stored vector good bounded
    (actualEvent ∘ actual.result) (idealEvent ∘ ideal.result) goodAgreement

/-- Relational output events retain their actual initial Store in the same coherent comparison. -/
theorem relational_event_le_add_four_mul_omitted_norm
    (actual : AlgorithmRun model pre actualPost actualShape)
    (ideal : AlgorithmRun model pre idealPost idealShape) {Reference : Register}
    (stored : Execution.Store pre × model.HiddenState)
    (vector : NormalizedVector (Register.prod pre.register Reference))
    (good : HilbertVector (Register.prod pre.register Reference)) (bounded : ‖good‖ ≤ 1)
    (actualEvent : Execution.Store pre × actualShape.Value → Bool)
    (idealEvent : Execution.Store pre × idealShape.Value → Bool)
    (goodAgreement :
      (actual.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (actual.recordEventEffects Reference
            (fun record => actualEvent (record.2.2.1, actual.result record))) =
      (ideal.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (ideal.recordEventEffects Reference
            (fun record => idealEvent (record.2.2.1, ideal.result record)))) :
    (ideal.relationalDistribution (pureInput (model := model) stored vector)).map idealEvent true ≤
      (actual.relationalDistribution (pureInput (model := model) stored vector)).map
          actualEvent true +
        ENNReal.ofReal (4 * ‖vector.vec - good‖) := by
  rw [relationalDistribution, relationalDistribution, PMF.map_comp, PMF.map_comp]
  exact execution_event_le_add_four_mul_omitted_norm actual ideal stored vector good bounded
    (fun record => actualEvent (record.2.2.1, actual.result record))
    (fun record => idealEvent (record.2.2.1, ideal.result record)) goodAgreement

end

end QuantumAlg.AlgorithmRun
