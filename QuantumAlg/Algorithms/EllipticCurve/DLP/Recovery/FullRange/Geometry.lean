/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Support
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Effect.BranchSupport
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Coherent full-range good and exceptional components

The complete full-range source retains an arbitrary coherent reference.  Its
admissible component remains unnormalized; the omitted norm is exactly the
square root of the full-range exceptional Born mass.  Certified effects that
agree on this component retain the full four-square-root comparison loss.
-/

namespace QuantumAlg.EllipticCurve.FullRange.Geometry

noncomputable section

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

open scoped BigOperators

/-- The complete pair of physical exponent registers as mathematical source coordinates. -/
abbrev branchRegister (width : Nat) : Register := (Qubits width).prod (Qubits width)

/-- The normalized state on every physical pair of exponent labels. -/
def bareState (width : Nat) : NormalizedVector (branchRegister width) :=
  NormalizedVector.prodTensor (exponentState width) (exponentState width)

lemma bareState_expansion (width : Nat) :
    (∑ branch : Branch width, branchAmplitude width branch •
      (NormalizedVector.ket (R := branchRegister width) branch).vec) =
      (bareState width).vec := by
  have coefficient (branch : Branch width) :
      branchAmplitude width branch = bareState width branch := by
    rw [bareState, NormalizedVector.prodTensor_apply]
    rfl
  simp_rw [coefficient]
  exact HilbertVector.sum_amplitude_smul_ket (bareState width).vec

/-- Full-range source with an arbitrary normalized coherent Reference factor. -/
def sourceState (width : Nat) {Reference : Register} (reference : NormalizedVector Reference) :
    NormalizedVector ((branchRegister width).prod Reference) :=
  NormalizedVector.prodTensor (bareState width) reference

variable {G : Type*} [Group G]

/-- The unnormalized admissible component, retaining every Reference amplitude. -/
def goodVector (width steps : Nat) (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference) :
    HilbertVector ((branchRegister width).prod Reference) :=
  HilbertVector.prodTensor
    (∑ branch ∈ admissibleBranches width steps selected addend seed,
      branchAmplitude width branch •
        (NormalizedVector.ket (R := branchRegister width) branch).vec) reference.vec

/-- Exact coordinates of the unnormalized full-range admissible component. -/
lemma goodVector_apply (width steps : Nat) (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference)
    (label : ((branchRegister width).prod Reference).Index) :
    goodVector width steps selected addend seed reference label =
      (if label.1 ∈ admissibleBranches width steps selected addend seed then
        branchAmplitude width label.1 else 0) * reference label.2 := by
  classical
  rw [goodVector, HilbertVector.prodTensor_apply]
  apply congrArg (fun amplitude : ℂ => amplitude * reference label.2)
  change (EuclideanSpace.projₗ (𝕜 := ℂ) label.1)
    (∑ branch ∈ admissibleBranches width steps selected addend seed,
      branchAmplitude width branch •
        (NormalizedVector.ket (R := branchRegister width) branch).vec) = _
  rw [map_sum]
  calc
    _ = ∑ branch ∈ admissibleBranches width steps selected addend seed,
        branchAmplitude width branch * (if label.1 = branch then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro branch _
      rw [map_smul]
      change branchAmplitude width branch *
        NormalizedVector.ket (R := branchRegister width) branch label.1 = _
      rw [NormalizedVector.ket_apply]
    _ = _ := by simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]

lemma goodVector_norm_le_one (width steps : Nat) (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference) :
    ‖goodVector width steps selected addend seed reference‖ ≤ 1 := by
  classical
  rw [goodVector, HilbertVector.norm_prodTensor, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_branch_sum_le_one (R := branchRegister width)
    Finset.univ (admissibleBranches width steps selected addend seed) (Finset.subset_univ _)
    id Function.injective_id (branchAmplitude width) (bareState width) (bareState_expansion width)

/-- Omission has exactly the full-range bad Born mass, without conditioning,
renormalization or an assumption about the external Reference vector. -/
lemma norm_sourceState_sub_goodVector (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference) :
    ‖(sourceState width reference).vec - goodVector width steps selected addend seed reference‖ =
      Real.sqrt (exceptionalMass width steps selected addend seed) := by
  classical
  let good : HilbertVector (branchRegister width) :=
    ∑ branch ∈ admissibleBranches width steps selected addend seed,
      branchAmplitude width branch •
        (NormalizedVector.ket (R := branchRegister width) branch).vec
  have difference : HilbertVector.prodTensor (bareState width).vec reference.vec -
      HilbertVector.prodTensor good reference.vec =
      HilbertVector.prodTensor ((bareState width).vec - good) reference.vec := by
    apply WithLp.ofLp_injective
    funext label
    exact (sub_mul _ _ _).symm
  change ‖HilbertVector.prodTensor (bareState width).vec reference.vec -
    HilbertVector.prodTensor good reference.vec‖ = _
  rw [difference, HilbertVector.norm_prodTensor, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_sub_branch_sum_eq_sqrt_bad (R := branchRegister width)
    Finset.univ (admissibleBranches width steps selected addend seed)
    (exceptionalBranches width steps selected addend seed)
    (branches_partition width steps selected addend seed)
    (branches_disjoint width steps selected addend seed) id Function.injective_id
    (branchAmplitude width) (bareState width).vec (bareState_expansion width)

/-- Agreement on every admissible pair of source coordinates retains all
off-diagonal Reference coherences in the complete good-density weight. -/
lemma goodVector_weight_eq_of_matrix (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference)
    (actual ideal : Effect ((branchRegister width).prod Reference))
    (agrees : ∀ left right : ((branchRegister width).prod Reference).Index,
      left.1 ∈ admissibleBranches width steps selected addend seed →
      right.1 ∈ admissibleBranches width steps selected addend seed →
      actual.matrix left right = ideal.matrix left right) :
    actual.weight (DensityOperator.ofSubnormalizedVector
      (goodVector width steps selected addend seed reference)
      (goodVector_norm_le_one width steps selected addend seed reference)) =
    ideal.weight (DensityOperator.ofSubnormalizedVector
      (goodVector width steps selected addend seed reference)
      (goodVector_norm_le_one width steps selected addend seed reference)) := by
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
  by_cases leftGood : left.1 ∈ admissibleBranches width steps selected addend seed
  · by_cases rightGood : right.1 ∈ admissibleBranches width steps selected addend seed
    · rw [agrees left right leftGood rightGood]
    · simp only [goodVector_apply, if_neg rightGood, zero_mul, mul_zero]
  · simp only [goodVector_apply, if_neg leftGood, zero_mul, star_zero, mul_zero]

/-- Certified actual and ideal effects agreeing on the full-range admissible
component differ by at most the complete four-square-root exceptional loss. -/
lemma effect_weight_le_add_four_sqrt (width steps : Nat)
    (selected : Branch width → Fin steps → Bool)
    (addend : Branch width → Fin steps → G) (seed : G) {Reference : Register}
    (reference : NormalizedVector Reference)
    (actual ideal : Effect ((branchRegister width).prod Reference))
    (agrees : actual.weight (DensityOperator.ofSubnormalizedVector
        (goodVector width steps selected addend seed reference)
        (goodVector_norm_le_one width steps selected addend seed reference)) =
      ideal.weight (DensityOperator.ofSubnormalizedVector
        (goodVector width steps selected addend seed reference)
        (goodVector_norm_le_one width steps selected addend seed reference))) :
    ideal.weight (DensityOperator.ofPure (sourceState width reference)) ≤
      actual.weight (DensityOperator.ofPure (sourceState width reference)) +
        4 * Real.sqrt (exceptionalMass width steps selected addend seed) := by
  have comparison := Effect.weight_le_add_four_mul_omitted_norm actual ideal
    (sourceState width reference) (goodVector width steps selected addend seed reference)
    (goodVector_norm_le_one width steps selected addend seed reference) agrees
  rw [norm_sourceState_sub_goodVector] at comparison
  exact comparison

end

end QuantumAlg.EllipticCurve.FullRange.Geometry
