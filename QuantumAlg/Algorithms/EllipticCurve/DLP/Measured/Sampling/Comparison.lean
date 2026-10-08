/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Execution
import all QuantumAlg.Core.Execution.Circuit.Support

/-!
# Original coherent error bound for sampling on the resident systems

The actual sampling prefix starts with arbitrary old classical values and
the same original quantum input in the already allocated workspace. Its
event observable agrees with the original group observable on the complete
good density. The original selected-frequency floor and exceptional error
therefore hold for this actual execution, before the terminal measurement.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP Canonical.Probability

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem actualEventWeight_compare {ctx : RuntimeCtx .quantum}
    (actual : Circuit (.quantum AlgorithmGate.model .empty) ctx ctx)
    (Reference : Register) (store : Store ctx)
    (input : NormalizedVector (ctx.register.prod Reference))
    (good : HilbertVector (ctx.register.prod Reference)) (bounded : ‖good‖ ≤ 1)
    (observed ideal : Effect (ctx.register.prod Reference))
    (agrees : observed.weight
      ((actual.execute Reference (ExecutionState.ofValue (store, ((), ()))
        (DensityOperator.ofSubnormalizedVector good bounded))).quantumMarginal) =
      ideal.weight (DensityOperator.ofSubnormalizedVector good bounded)) :
    ideal.weight (DensityOperator.ofPure input) ≤
      observed.weight ((actual.execute Reference (ExecutionState.ofValue (store, ((), ()))
        (DensityOperator.ofPure input))).quantumMarginal) + 4 * ‖input.vec - good‖ := by
  let pulled := actual.effectPullback Reference (fun _ => observed) (store, ((), ()))
  have goodWeight := actual.effectWeight_execute Reference
    (ExecutionState.ofValue (store, ((), ()))
      (DensityOperator.ofSubnormalizedVector good bounded))
    (fun _ => observed)
  rw [ExecutionState.effectWeight_constant, ExecutionState.effectWeight_ofValue_decision]
    at goodWeight
  have inputWeight := actual.effectWeight_execute Reference
    (ExecutionState.ofValue (store, ((), ())) (DensityOperator.ofPure input))
    (fun _ => observed)
  rw [ExecutionState.effectWeight_constant, ExecutionState.effectWeight_ofValue_decision]
    at inputWeight
  rw [inputWeight]
  exact Effect.weight_le_add_four_mul_omitted_norm pulled ideal input good bounded
    (goodWeight.symm.trans agrees)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The actual resident sampling prefix retains the original coherent error constant. -/
theorem idealInputWeight_le_samplingPrefixWeight_add
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (store : Store (after p.size (2 * orderWidth problem)))
    (ideal : Effect ((before p.size (2 * orderWidth problem)).register.prod Reference))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (agrees :
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event Reference).weight
        (preMeasurementDensity E fieldTail odd problem points Reference
          (DensityOperator.ofSubnormalizedVector
            (goodInputVector problem fieldTail sameWidth fits points seed reference)
            (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference))) =
        ideal.weight (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference))) :
    ideal.weight (DensityOperator.ofPure
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)) ≤
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event Reference).weight
        (((samplingPrefix E fieldTail odd problem points).execute Reference
          (ExecutionState.ofValue (store, ((), ())) (DensityOperator.ofPure
            (samplingInputVector problem fieldTail sameWidth fits seed
              reference)))).quantumMarginal) +
        4 * Real.sqrt (preparedExceptionalMass problem points seed) := by
  let embedding := initializedOutputEmbedding p (2 * orderWidth problem) Reference
  have injective := initializedOutputEmbedding_injective p (2 * orderWidth problem) Reference
  let extended := Effect.extend embedding injective ideal
  let originalGood := DensityOperator.ofSubnormalizedVector
    (goodInputVector problem fieldTail sameWidth fits points seed reference)
    (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  let residentGood := DensityOperator.ofSubnormalizedVector
    (samplingGoodVector problem fieldTail sameWidth fits points seed reference)
    (samplingGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  let goodState : State (after p.size (2 * orderWidth problem)) Reference
      (ClassicalOracleModel.empty.HiddenState × Unit) :=
    ExecutionState.ofValue (store, ((), ())) residentGood
  have initialized : goodState.quantumMarginal =
      initializedDensity p (2 * orderWidth problem) Reference originalGood := by
    simp only [goodState, ExecutionState.ofValue_quantumMarginal]
    exact samplingGoodVector_density problem fieldTail sameWidth fits points seed reference
  have actualGood := samplingPrefix_density_of_initialized E fieldTail sameWidth fits odd
    problem points seed goodState originalGood initialized
    (goodInputVector_prepared_supported problem fieldTail sameWidth fits points seed reference)
  have extendedGood : extended.weight residentGood = ideal.weight originalGood :=
    Effect.extend_weight_ofSubnormalizedVector embedding injective ideal
      (goodInputVector problem fieldTail sameWidth fits points seed reference)
      (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  have comparison := actualEventWeight_compare (samplingPrefix E fieldTail odd problem points)
    Reference store (samplingInputVector problem fieldTail sameWidth fits seed reference)
    (samplingGoodVector problem fieldTail sameWidth fits points seed reference)
    (samplingGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
    (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem)) event Reference)
    extended (by rw [actualGood, extendedGood]; exact agrees)
  have extendedInput : extended.weight (DensityOperator.ofPure
      (samplingInputVector problem fieldTail sameWidth fits seed reference)) =
      ideal.weight (DensityOperator.ofPure
        (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)) := by
    rw [← DensityOperator.ofSubnormalizedVector_of_normalized
      (samplingInputVector problem fieldTail sameWidth fits seed reference),
      ← DensityOperator.ofSubnormalizedVector_of_normalized
        (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)]
    exact Effect.extend_weight_ofSubnormalizedVector embedding injective ideal
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec
      (by rw [(originalMontgomeryInputVector problem fieldTail sameWidth fits seed
        reference).norm_eq_one])
  rw [extendedInput, norm_samplingInput_sub_good] at comparison
  exact comparison

/-- The original selected-frequency floor holds for the actual prefix with every old Store. -/
theorem selectedSamplingPrefix_weight_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (input : SecretInput problem) {Reference : Register}
    (reference : NormalizedVector Reference)
    (store : Store (after p.size (2 * orderWidth problem))) :
    (problem.order : ℝ) * Nat.totient problem.order /
      (4 * (fourierModulus problem : ℝ) ^ 2) ≤
      (QubitReadouts.eventEffect (afterExponentWires p (orderWidth problem))
        (selectedExponentEvent problem input) Reference).weight
        (((samplingPrefix E fieldTail odd problem points).execute Reference
          (ExecutionState.ofValue (store, ((), ())) (DensityOperator.ofPure
            (samplingInputVector problem fieldTail sameWidth fits seed
              reference)))).quantumMarginal) +
        4 * Real.sqrt (preparedExceptionalMass problem points seed) := by
  have agrees := idealInputEffect_goodAgreement problem fieldTail sameWidth fits odd points seed
    addends (selectedExponentEvent problem input) reference
  rw [exponentRunDensity_eventWeight] at agrees
  have actual := idealInputWeight_le_samplingPrefixWeight_add E fieldTail sameWidth fits odd
    problem points seed reference store
    (idealInputEffect problem fieldTail sameWidth fits seed
      (selectedExponentEvent problem input) Reference)
    (selectedExponentEvent problem input) agrees
  exact (idealInputEffect_selected_lower problem fieldTail sameWidth fits seed input
    reference).trans actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
