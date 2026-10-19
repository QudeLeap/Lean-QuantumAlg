/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.SourceGeometry
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.PreparedSupport
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Probability
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.QuadraticStability
import all QuantumAlg.Core.Base.Gate.Effect.Support
import all QuantumAlg.Core.Base.Gate.Effect.Extension
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.State.Density.Vector

/-!
# Original good-column matrix agreement keeps every coherent cross term

The unchanged original good vector has support precisely inside the original
admissible branch set. Equality of all matrix entries between those branches
therefore gives equality of the full good-density weights, beside arbitrary
Reference coherences. No normalization or conditioning of the good component
is performed. The actual event kernel must still supply the entry equality.

The unchanged original selected event gives its pure-state lower bound after
the existing four-square-root exceptional loss. This internal implication
still requires the exact original-good matrix entries; it supplies no actual
execution agreement certificate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace GoodKernelAgreement

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP
open QuantumAlg.FiniteCyclicDLP.Canonical.Probability
open ECDLP.Measured
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original coherent good vector keeps its exact unnormalized branch and Reference factors. -/
lemma goodVector_apply (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (label : ((idealBranchRegister problem).prod Reference).Index) :
    SourceGeometry.goodVector problem points seed reference label =
      (if label.1 ∈ preparedAdmissibleBranches problem points seed
        then preparedBranchAmplitude problem label.1 else 0) * reference label.2 := by
  classical
  rw [SourceGeometry.goodVector, HilbertVector.prodTensor_apply]
  apply congrArg (fun amplitude : ℂ => amplitude * reference label.2)
  have coordinate (R : Register) (branches : Finset R.Index)
      (amplitude : R.Index → ℂ) (index : R.Index) :
      (EuclideanSpace.projₗ (𝕜 := ℂ) index)
          (∑ branch ∈ branches,
            amplitude branch • (NormalizedVector.ket (R := R) branch).vec) =
        if index ∈ branches then amplitude index else 0 := by
    rw [map_sum]
    calc
      (∑ branch ∈ branches, (EuclideanSpace.projₗ (𝕜 := ℂ) index)
          (amplitude branch • (NormalizedVector.ket (R := R) branch).vec)) =
          ∑ branch ∈ branches, amplitude branch * (if index = branch then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro branch _member
        rw [map_smul]
        change amplitude branch * NormalizedVector.ket (R := R) branch index = _
        rw [NormalizedVector.ket_apply]
      _ = _ := by simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
  change (EuclideanSpace.projₗ (𝕜 := ℂ) label.1)
    (∑ branch ∈ preparedAdmissibleBranches problem points seed,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (R := idealBranchRegister problem) branch).vec) = _
  exact (coordinate (idealBranchRegister problem)
    (preparedAdmissibleBranches problem points seed) (preparedBranchAmplitude problem)
    label.1).trans
      (congrArg (fun decision : Decidable (label.1 ∈
          preparedAdmissibleBranches problem points seed) =>
        @ite ℂ _ decision (preparedBranchAmplitude problem label.1) 0)
        (Subsingleton.elim _ _))

/-- Agreement on every pair of original good branches gives their complete density weight. -/
lemma goodVector_weight_eq_of_matrix (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (actual ideal : Effect ((idealBranchRegister problem).prod Reference))
    (agrees : ∀ left right : ((idealBranchRegister problem).prod Reference).Index,
      left.1 ∈ preparedAdmissibleBranches problem points seed →
      right.1 ∈ preparedAdmissibleBranches problem points seed →
      actual.matrix left right = ideal.matrix left right) :
    actual.weight (DensityOperator.ofSubnormalizedVector
        (SourceGeometry.goodVector problem points seed reference)
        (SourceGeometry.goodVector_norm_le_one problem points seed reference)) =
      ideal.weight (DensityOperator.ofSubnormalizedVector
        (SourceGeometry.goodVector problem points seed reference)
        (SourceGeometry.goodVector_norm_le_one problem points seed reference)) := by
  classical
  rw [Effect.weight_ofSubnormalizedVector, Effect.weight_ofSubnormalizedVector]
  unfold HilbertOperator.quadraticWeight
  apply congrArg Complex.re
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    HilbertOperator.applyVec_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  by_cases leftGood : left.1 ∈ preparedAdmissibleBranches problem points seed
  · by_cases rightGood : right.1 ∈ preparedAdmissibleBranches problem points seed
    · rw [agrees left right leftGood rightGood]
    · simp only [goodVector_apply, if_neg rightGood, zero_mul, mul_zero]
  · simp only [goodVector_apply, if_neg leftGood, zero_mul, star_zero, mul_zero]

/-- The same original source state gives exactly the retained ideal Fourier readout weight. -/
lemma idealBranchEffect_sourceState_weight (problem : KnownOrderProblem E.GroupPoint)
    (seed : AffinePoint E) (event : (Fin (2 * orderWidth problem) → Bool) → Bool)
    {Reference : Register} (reference : NormalizedVector Reference) :
    (idealBranchEffect problem seed event Reference).weight
        (DensityOperator.ofPure (SourceGeometry.sourceState problem reference)) =
      (idealReadoutEffect problem seed event Reference).weight
        (DensityOperator.ofPure (ECDLP.Measured.idealFourierState problem seed reference)) := by
  let prepared := ECDLP.Measured.idealPreparedBranchState problem reference
  let extended : NormalizedVector (((Qubits (orderWidth problem + orderWidth problem)).prod
      (idealGroupRegister problem seed)).prod Reference) :=
    NormalizedVector.ofVector
      (Effect.extensionVector (idealOracleEmbedding problem seed Reference) prepared.vec)
      (by rw [Effect.norm_extensionVector _
            (idealOracleEmbedding_injective problem seed Reference), prepared.norm_eq_one])
  have preparedBound : ‖prepared.vec‖ ≤ 1 := by rw [prepared.norm_eq_one]
  have extendedBound : ‖extended.vec‖ ≤ 1 := by rw [extended.norm_eq_one]
  have bridge := idealBranchEffect_weight problem seed event Reference prepared.vec preparedBound
  change (idealBranchEffect problem seed event Reference).weight
      (DensityOperator.ofSubnormalizedVector prepared.vec preparedBound) =
    (idealReadoutEffect problem seed event Reference).weight
      (DensityOperator.applyUnitary (idealReadoutOperator problem seed Reference)
        (DensityOperator.ofSubnormalizedVector extended.vec extendedBound)) at bridge
  simp only [DensityOperator.ofSubnormalizedVector_of_normalized] at bridge
  rw [← DensityOperator.ofPure_apply] at bridge
  have preparedSame : prepared = SourceGeometry.sourceState problem reference := rfl
  have fourierSame : (idealReadoutOperator problem seed Reference).apply extended =
      ECDLP.Measured.idealFourierState problem seed reference := rfl
  simpa only [preparedSame, fourierSame] using bridge

/-- Original-good matrix agreement retains the original selected lower bound and loss. -/
lemma selected_effect_lower_of_good_matrix (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    (input : SecretInput problem) {Reference : Register}
    (reference : NormalizedVector Reference)
    (actual : Effect ((idealBranchRegister problem).prod Reference))
    (agrees : ∀ left right : ((idealBranchRegister problem).prod Reference).Index,
      left.1 ∈ preparedAdmissibleBranches problem points seed →
      right.1 ∈ preparedAdmissibleBranches problem points seed →
      actual.matrix left right =
        (idealBranchEffect problem seed (ECDLP.Measured.selectedExponentEvent problem input)
          Reference).matrix left right) :
    (problem.order : ℝ) * Nat.totient problem.order /
        (4 * (fourierModulus problem : ℝ) ^ 2) -
        4 * Real.sqrt (preparedExceptionalMass problem points seed) ≤
      actual.weight (DensityOperator.ofPure (SourceGeometry.sourceState problem reference)) := by
  have goodAgrees := goodVector_weight_eq_of_matrix problem points seed reference actual
    (idealBranchEffect problem seed (ECDLP.Measured.selectedExponentEvent problem input)
      Reference) agrees
  have stability := SourceGeometry.effect_weight_le_add_four_sqrt problem points seed reference
    actual (idealBranchEffect problem seed (ECDLP.Measured.selectedExponentEvent problem input)
      Reference) goodAgrees
  have lower := ECDLP.Measured.idealReadoutEffect_selected_lower problem seed input reference
  rw [← idealBranchEffect_sourceState_weight problem seed
    (ECDLP.Measured.selectedExponentEvent problem input) reference] at lower
  exact sub_le_iff_le_add.mpr (lower.trans stability)

end

end GoodKernelAgreement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
