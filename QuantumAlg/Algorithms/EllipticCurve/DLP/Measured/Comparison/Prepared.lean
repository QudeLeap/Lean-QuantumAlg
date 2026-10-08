/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Comparison
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Offset

/-!
# Original prepared input and fixed-offset output probability comparison

The actual input has zero exponents, the supplied Montgomery seed, and an
arbitrary normalized reference. Its good component is transported by the
actual preparation adjoint, with no renormalization. The original coherent
decomposition therefore gives the original four-times-square-root exceptional
mass error for the true output PMF.

Finite averaging chooses one original nonidentity subgroup offset with the
original two-exceptions-per-step bound. Only equality with the mathematical
target observable on the full coherent good density remains a premise here;
support, preparation, and the omitted norm are derived from the original input.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original supplied input retains exactly the original exceptional-mass error. -/
theorem idealEventWeight_le_originalRunProbability_add
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (stored : Store (before p.size (2 * orderWidth problem)))
    (ideal : Effect (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (idealAgreement :
      (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
        event Reference).weight
          (exponentRunDensity E fieldTail odd problem points Reference
            (DensityOperator.ofSubnormalizedVector
              (goodInputVector problem fieldTail sameWidth fits points seed reference)
              (goodInputVector_norm_le_one problem fieldTail sameWidth fits
                points seed reference))) =
        ideal.weight (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits
            points seed reference))) :
    ENNReal.ofReal (ideal.weight (DensityOperator.ofPure
      (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))) ≤
      ((exponentRun E fieldTail odd problem points).outputDistribution
        (AlgorithmRun.pureInput (stored, ())
          (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))).map
            (fun value => event (QubitReadouts.mask value)) true +
        ENNReal.ofReal (4 * Real.sqrt (preparedExceptionalMass problem points seed)) := by
  have comparison := idealEventWeight_le_exponentRunProbability_add E fieldTail sameWidth fits
    odd problem points seed stored
    (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference)
    (goodInputVector problem fieldTail sameWidth fits points seed reference)
    (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
    ideal event
    (goodInputVector_prepared_supported problem fieldTail sameWidth fits points seed reference)
    idealAgreement
  rw [norm_originalMontgomeryInput_sub_good] at comparison
  exact comparison

/-- One original subgroup offset gives the original constant for the actual output PMF. -/
theorem exists_fixedOffset_originalRunProbability_bound
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint) (orderAtLeastTwo : 2 ≤ problem.order)
    (points : Fin (2 * orderWidth problem) → AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (stored : Store (before p.size (2 * orderWidth problem)))
    (ideal : AffinePoint E →
      Effect (Register.prod (before p.size (2 * orderWidth problem)).register Reference))
    (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    (idealAgreement : ∀ seed : AffinePoint E,
      (QubitReadouts.eventEffect (exponentMeasurementWires p (orderWidth problem))
        event Reference).weight
          (exponentRunDensity E fieldTail odd problem points Reference
            (DensityOperator.ofSubnormalizedVector
              (goodInputVector problem fieldTail sameWidth fits points seed reference)
              (goodInputVector_norm_le_one problem fieldTail sameWidth fits
                points seed reference))) =
        (ideal seed).weight (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits
            points seed reference))) :
    ∃ seed : AffinePoint E,
      seed.toGroupPoint ∈ Subgroup.zpowers problem.generator ∧ seed.toGroupPoint ≠ 1 ∧
        ENNReal.ofReal ((ideal seed).weight (DensityOperator.ofPure
          (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference))) ≤
          ((exponentRun E fieldTail odd problem points).outputDistribution
            (AlgorithmRun.pureInput (stored, ())
              (originalMontgomeryInputVector problem fieldTail sameWidth fits
                seed reference))).map
                  (fun value => event (QubitReadouts.mask value)) true +
            ENNReal.ofReal (4 * Real.sqrt
              ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ))) := by
  obtain ⟨seed, member, nonidentity, massBound⟩ :=
    exists_fixedOffset_exceptionalMass_bound problem orderAtLeastTwo points
  refine ⟨seed, member, nonidentity, ?_⟩
  have comparison := idealEventWeight_le_originalRunProbability_add E fieldTail sameWidth fits
    odd problem points seed reference stored (ideal seed) event (idealAgreement seed)
  have omittedBound : 4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤
      4 * Real.sqrt
        ((2 * (2 * orderWidth problem) : Nat) / ((problem.order - 1 : Nat) : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt massBound) (by norm_num)
  exact comparison.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal omittedBound))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
