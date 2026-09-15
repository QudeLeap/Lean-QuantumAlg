/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Run
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Support

/-!
# Coherent event comparison for the actual measured scalar run

The actual run includes both original exponent programs, the measured scalar
implementation, fresh terminal result cells, and its complete structural
Output. Its true output event probability is compared with a certified
mathematical effect on the same complete input register and reference.

The agreement hypothesis concerns the full coherent good density after the
independently specified scalar target and readout. Actual good-event equality
is obtained from the original active-step domain and the execution theorem;
it is not supplied as a replacement interpretation. No ideal circuit or gate
is constructed from the mathematical group action.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP

private theorem outputProbability_bound_by_inputEffect
    {pre post : RuntimeCtx .quantum} {shape : CShape}
    (actual : AlgorithmRun pre post shape) {Reference : Register}
    (stored : Store pre) (vector : NormalizedVector (Register.prod pre.register Reference))
    (good : HilbertVector (Register.prod pre.register Reference)) (bounded : ‖good‖ ≤ 1)
    (ideal : Effect (Register.prod pre.register Reference)) (event : shape.Value → Bool)
    (agrees :
      (actual.execute Reference (ExecutionState.ofValue stored
        (DensityOperator.ofSubnormalizedVector good bounded))).effectWeight
          (actual.recordEventEffects Reference (event ∘ actual.result)) =
      ideal.weight (DensityOperator.ofSubnormalizedVector good bounded)) :
    ENNReal.ofReal (ideal.weight (DensityOperator.ofPure vector)) ≤
      (actual.outputDistribution (AlgorithmRun.pureInput stored vector)).map event true +
        ENNReal.ofReal (4 * ‖vector.vec - good‖) := by
  let actualEffect := actual.effectPullback Reference
    (actual.recordEventEffects Reference (event ∘ actual.result)) stored
  have actualGood := actual.effectWeight_execute Reference
    (ExecutionState.ofValue stored (DensityOperator.ofSubnormalizedVector good bounded))
    (actual.recordEventEffects Reference (event ∘ actual.result))
  rw [ExecutionState.effectWeight_ofValue] at actualGood
  have comparison := Effect.weight_le_add_four_mul_omitted_norm actualEffect ideal vector
    good bounded (actualGood.symm.trans agrees)
  have probability :
      (actual.outputDistribution (AlgorithmRun.pureInput stored vector)).map event true =
        ENNReal.ofReal (actualEffect.weight (DensityOperator.ofPure vector)) :=
    (actual.outputDistribution_event_eq_input_effectWeight
      (AlgorithmRun.pureInput stored vector) event).trans (congrArg ENNReal.ofReal
        (ExecutionState.effectWeight_ofValue stored (DensityOperator.ofPure vector)
          (actual.effectPullback Reference
            (actual.recordEventEffects Reference (event ∘ actual.result)))))
  rw [probability]
  exact (ENNReal.ofReal_le_ofReal comparison).trans ENNReal.ofReal_add_le

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual output probability retains the original four-times-omitted-norm bound. -/
theorem idealEventWeight_le_exponentRunProbability_add
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (stored : Store (before p.size (2 * orderWidth problem)))
    (vector : NormalizedVector
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (good : HilbertVector
      (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (bounded : ‖good‖ ≤ 1)
    (ideal : Effect (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (support : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference
          (DensityOperator.ofSubnormalizedVector good bounded)).matrix basis basis = 0)
    (idealAgreement :
      (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
        event Reference).weight
          (exponentRunDensity E fieldTail odd problem points Reference
            (DensityOperator.ofSubnormalizedVector good bounded)) =
        ideal.weight (DensityOperator.ofSubnormalizedVector good bounded)) :
    ENNReal.ofReal (ideal.weight (DensityOperator.ofPure vector)) ≤
      ((exponentRun E fieldTail odd problem points).outputDistribution
        (AlgorithmRun.pureInput stored vector)).map
          (fun value => event (QubitReadouts.mask value)) true +
        ENNReal.ofReal (4 * ‖vector.vec - good‖) := by
  apply outputProbability_bound_by_inputEffect
    (exponentRun E fieldTail odd problem points) stored vector good bounded ideal
    (fun value => event (QubitReadouts.mask value))
  let input := ExecutionState.ofValue stored
    (DensityOperator.ofSubnormalizedVector good bounded)
  have original : input.quantumMarginal =
      DensityOperator.ofSubnormalizedVector good bounded :=
    ExecutionState.ofValue_quantumMarginal stored _
  have supported : ∀ basis,
      ¬Encoding.pairedMontgomeryAllowed E fieldTail sameWidth fits points seed basis.1 →
        (exponentPreparedDensity E problem Reference input.quantumMarginal).matrix
          basis basis = 0 := by
    rw [original]
    exact support
  have actual := exponentRun_eventWeight E fieldTail sameWidth fits odd problem points seed
    input supported event
  rw [original] at actual
  exact actual.trans idealAgreement

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
