/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.SourceGeometry
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.FreeSourceFamily
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Original source geometry in the actual free-source binary coordinates

The binary tuples are mathematical source coordinates, beside the complete
unchanged bank. The basis equivalence transports the original pair of range
states and its unnormalized good component. In particular, the same omitted
norm is retained before any selected actual effect is supplied.

These statements do not certify the actual free-source Gram identity or its
agreement with the ideal effect. They allocate no register and make no
success-floor, runtime-retirement or physical input-support claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace BinarySourceGeometry

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates Recovery.Conversion.FreeSourceFamily
open ECDLP.Measured
open scoped BigOperators

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- This mathematical register retains the entire actual bank and its external reference. -/
def bankRegister (width m : Nat) (Reference : Register) : Register where
  Index := Bank width m Reference
  fintype := inferInstance
  decEq := inferInstance

/-- The original first/second labels become the same ordered pair of binary tuples. -/
def sourceBasis (problem : KnownOrderProblem E.GroupPoint) (Reference : Register) :
    ((idealBranchRegister problem).prod
      (bankRegister p.size (orderWidth problem) Reference)).Index ≃
        (sourceRegister p.size (orderWidth problem) Reference).Index :=
  Equiv.prodCongr
    (Equiv.prodCongr (binaryEquiv (orderWidth problem)).symm
      (binaryEquiv (orderWidth problem)).symm)
    (Equiv.refl (Bank p.size (orderWidth problem) Reference))

/-- The complete normalized source is the original coherent source in those coordinates. -/
def sourceState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference)) :
    NormalizedVector (sourceRegister p.size (orderWidth problem) Reference) :=
  NormalizedVector.reindex
    (R := (idealBranchRegister problem).prod
      (bankRegister p.size (orderWidth problem) Reference))
    (S := sourceRegister p.size (orderWidth problem) Reference) (sourceBasis problem Reference)
    (SourceGeometry.sourceState problem reference)

/-- The unnormalized original good component is transported without conditioning. -/
def goodVector (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference)) :
    HilbertVector (sourceRegister p.size (orderWidth problem) Reference) :=
  HilbertVector.reindex
    (R := (idealBranchRegister problem).prod
      (bankRegister p.size (orderWidth problem) Reference))
    (S := sourceRegister p.size (orderWidth problem) Reference) (sourceBasis problem Reference)
    (SourceGeometry.goodVector problem points seed reference)

private lemma original_range_amplitude (problem : KnownOrderProblem E.GroupPoint)
    (index : Fin (2 ^ orderWidth problem)) :
    Concrete.BornBridge.exponentState problem index =
      ((if index.val < problem.order then invSqrt problem.order else 0 : ℝ) : ℂ) := by
  rw [Concrete.BornBridge.exponentState_apply]
  split_ifs
  · simp only [FiniteCyclicDLP.invSqrtOrder, invSqrt, Complex.ofReal_inv]
  · rfl

/-- The literal preparation amplitudes are exactly the original range-state amplitudes. -/
lemma sourceState_apply (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference))
    (output : (sourceRegister p.size (orderWidth problem) Reference).Index) :
    sourceState problem reference output =
      preparationAmplitude (orderWidth problem) problem.order output.1 * reference output.2 := by
  change
    (Concrete.BornBridge.exponentState problem
        (binaryEquiv (orderWidth problem) output.1.1) *
      Concrete.BornBridge.exponentState problem
        (binaryEquiv (orderWidth problem) output.1.2)) * reference output.2 = _
  rw [original_range_amplitude, original_range_amplitude]
  exact congrArg (fun amplitude : ℂ => amplitude * reference output.2) (mul_comm _ _)

/-- The actual rectangular preparation columns give this same normalized vector. -/
lemma preparationColumns_sourceState (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference)) :
    (preparationColumns p.size (orderWidth problem) problem.order Reference).toEuclideanLin
        reference.vec = (sourceState problem reference).vec := by
  classical
  apply WithLp.ofLp_injective
  funext output
  change (∑ input : Bank p.size (orderWidth problem) Reference,
    (preparationAmplitude (orderWidth problem) problem.order output.1 *
      if output.2 = input then 1 else 0) * reference input) = sourceState problem reference output
  rw [sourceState_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_ite_eq]

/-- Binary reindexing keeps the same coherent good component's norm bound. -/
lemma goodVector_norm_le_one (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference)) :
    ‖goodVector problem points seed reference‖ ≤ 1 := by
  rw [goodVector, HilbertVector.norm_reindex
    (R := (idealBranchRegister problem).prod
      (bankRegister p.size (orderWidth problem) Reference))
    (S := sourceRegister p.size (orderWidth problem) Reference)]
  exact SourceGeometry.goodVector_norm_le_one problem points seed reference

/-- The loss is still the original exceptional square root, including its zero case. -/
lemma norm_sourceState_sub_goodVector (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference)) :
    ‖(sourceState problem reference).vec - goodVector problem points seed reference‖ =
      Real.sqrt (preparedExceptionalMass problem points seed) := by
  have difference :
      (sourceState problem reference).vec - goodVector problem points seed reference =
        HilbertVector.reindex
          (R := (idealBranchRegister problem).prod
            (bankRegister p.size (orderWidth problem) Reference))
          (S := sourceRegister p.size (orderWidth problem) Reference)
          (sourceBasis problem Reference)
          ((SourceGeometry.sourceState problem reference).vec -
            SourceGeometry.goodVector problem points seed reference) := by
    apply WithLp.ofLp_injective
    funext output
    rfl
  rw [difference, HilbertVector.norm_reindex
    (R := (idealBranchRegister problem).prod
      (bankRegister p.size (orderWidth problem) Reference))
    (S := sourceRegister p.size (orderWidth problem) Reference)]
  exact SourceGeometry.norm_sourceState_sub_goodVector problem points seed reference

/-- Effects on the actual free-source coordinates obey the same good-component comparison. -/
lemma effect_weight_le_add_four_sqrt (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register}
    (reference : NormalizedVector (bankRegister p.size (orderWidth problem) Reference))
    (actual ideal : Effect (sourceRegister p.size (orderWidth problem) Reference))
    (agrees : actual.weight (DensityOperator.ofSubnormalizedVector
        (goodVector problem points seed reference)
        (goodVector_norm_le_one problem points seed reference)) =
      ideal.weight (DensityOperator.ofSubnormalizedVector
        (goodVector problem points seed reference)
        (goodVector_norm_le_one problem points seed reference))) :
    ideal.weight (DensityOperator.ofPure (sourceState problem reference)) ≤
      actual.weight (DensityOperator.ofPure (sourceState problem reference)) +
        4 * Real.sqrt (preparedExceptionalMass problem points seed) := by
  have comparison := Effect.weight_le_add_four_mul_omitted_norm actual ideal
    (sourceState problem reference) (goodVector problem points seed reference)
    (goodVector_norm_le_one problem points seed reference) agrees
  rw [norm_sourceState_sub_goodVector] at comparison
  exact comparison

end

end BinarySourceGeometry
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
