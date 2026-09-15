/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Program

/-!
# Original input coordinates for the coherent prepared good component

The adjoint of the actual exponent preparation transports the good component
back to the original input vector space. This is a mathematical decomposition
of the supplied input; it adds no circuit and performs no measurement or
renormalization. The exact prepared density has the original admissible support,
and the omitted norm is unchanged by the same actual unitary preparation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding
open FiniteCyclicDLP ConcreteCircuitAccess

private theorem applyUnitary_subnormalizedVector {R : Register}
    (operator : UnitaryOperator R) (vector : HilbertVector R) (bounded : ‖vector‖ ≤ 1) :
    DensityOperator.applyUnitary operator (DensityOperator.ofSubnormalizedVector vector bounded) =
      DensityOperator.ofSubnormalizedVector (operator.applyVec vector)
        (by rw [operator.norm_applyVec]; exact bounded) := by
  symm
  apply DensityOperator.ext
  ext row column
  change (∑ left, operator row left * vector left) *
      star (∑ right, operator column right * vector right) =
    ∑ right, (∑ left, operator row left * (vector left * star (vector right))) *
      star (operator column right)
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro left _
  ring

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]

/-- The actual original input has zero exponents, supplied Montgomery seed, and full reference. -/
def originalMontgomeryInputVector (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector (Register.prod (before p.size (2 * orderWidth problem)).register Reference) :=
  normalizedReferenceFrame (NormalizedVector.ket
    (pairedMontgomeryInput fieldTail (orderWidth problem) sameWidth fits seed (0, 0))) reference

/-- The original input's actual exponent preparation is the complete certified prepared vector. -/
theorem originalMontgomeryInputVector_prepared (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem) Reference).applyVec
        (originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec =
      (preparedMontgomeryVector problem fieldTail sameWidth fits seed reference).vec :=
  preparedMontgomeryVector_actual problem fieldTail sameWidth fits seed reference

/-- The actual preparation adjoint pulls the good component to original input coordinates. -/
def goodInputVector (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector (Register.prod (before p.size (2 * orderWidth problem)).register Reference) :=
  (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
    (exponentPreparationCircuit_physical_idx problem) Reference).dagger.applyVec
      (preparedGoodVector problem fieldTail sameWidth fits points seed reference)

/-- Pulling back the good component preserves its original subnormalized norm. -/
theorem goodInputVector_norm_le_one (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖goodInputVector problem fieldTail sameWidth fits points seed reference‖ ≤ 1 := by
  rw [goodInputVector, UnitaryOperator.norm_applyVec]
  exact preparedGoodVector_norm_le_one problem fieldTail sameWidth fits points seed reference

/-- The same actual preparation returns exactly the complete coherent prepared good vector. -/
theorem goodInputVector_prepared (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem) Reference).applyVec
        (goodInputVector problem fieldTail sameWidth fits points seed reference) =
      preparedGoodVector problem fieldTail sameWidth fits points seed reference := by
  rw [goodInputVector, ← UnitaryOperator.mul_applyVec, UnitaryOperator.dagger,
    mul_inv_cancel, UnitaryOperator.one_applyVec]

/-- The actual prepared density is exactly the unrenormalized rank-one good density. -/
theorem goodInputVector_preparedDensity (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    exponentPreparedDensity E problem Reference
      (DensityOperator.ofSubnormalizedVector
        (goodInputVector problem fieldTail sameWidth fits points seed reference)
        (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)) =
      DensityOperator.ofSubnormalizedVector
        (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
        (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
          points seed reference) := by
  have transformed := applyUnitary_subnormalizedVector
    (beforeExponentOperator p (orderWidth problem) (exponentPreparationCircuit problem)
      (exponentPreparationCircuit_physical_idx problem) Reference)
    (goodInputVector problem fieldTail sameWidth fits points seed reference)
    (goodInputVector_norm_le_one problem fieldTail sameWidth fits points seed reference)
  apply DensityOperator.ext
  refine (congrArg DensityOperator.matrix transformed).trans ?_
  ext row column
  simp only [DensityOperator.ofSubnormalizedVector_matrix, goodInputVector_prepared]

/-- The prepared good-input density satisfies the original actual scalar admissible support. -/
theorem goodInputVector_prepared_supported (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ∀ label, ¬pairedMontgomeryAllowed E fieldTail sameWidth fits points seed label.1 →
      (exponentPreparedDensity E problem Reference
        (DensityOperator.ofSubnormalizedVector
          (goodInputVector problem fieldTail sameWidth fits points seed reference)
          (goodInputVector_norm_le_one problem fieldTail sameWidth fits
            points seed reference))).matrix label label = 0 := by
  rw [goodInputVector_preparedDensity]
  exact preparedGoodDensity_supported problem fieldTail sameWidth fits points seed reference

/-- The original-input decomposition keeps precisely the original exceptional omitted norm. -/
theorem norm_originalMontgomeryInput_sub_good (problem : KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖(originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec -
      goodInputVector problem fieldTail sameWidth fits points seed reference‖ =
      Real.sqrt (preparedExceptionalMass problem points seed) := by
  have isometry := (beforeExponentOperator p (orderWidth problem)
    (exponentPreparationCircuit problem) (exponentPreparationCircuit_physical_idx problem)
    Reference).norm_applyVec
      ((originalMontgomeryInputVector problem fieldTail sameWidth fits seed reference).vec -
        goodInputVector problem fieldTail sameWidth fits points seed reference)
  rw [UnitaryOperator.applyVec_sub, originalMontgomeryInputVector_prepared,
    goodInputVector_prepared] at isometry
  exact isometry.symm.trans
    (norm_preparedMontgomery_sub_good problem fieldTail sameWidth fits points seed reference)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
