/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.PreparedSupport
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Effect.BranchSupport
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# Original coherent source geometry before any physical encoding

The original two range states give a normalized mathematical source vector.
Its admissible component stays unnormalized, and its omitted norm is exactly
the square root of the original exceptional mass, beside an arbitrary
normalized reference. No physical register is allocated by these definitions.
The final conditional effect lemma supplies no actual streaming effect or
agreement certificate; those remain separate execution proof obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.SourceGeometry

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP
open ECDLP.Measured
open scoped BigOperators

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original independent range states, with no physical input representation. -/
def bareState (problem : KnownOrderProblem E.GroupPoint) :
    NormalizedVector (idealBranchRegister problem) :=
  NormalizedVector.prodTensor (Concrete.BornBridge.exponentState problem)
    (Concrete.BornBridge.exponentState problem)

/-- The source expansion retains exactly its original range and amplitudes. -/
lemma bareState_expansion (problem : KnownOrderProblem E.GroupPoint) :
    (∑ branch ∈ preparedSourceBranches problem,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (R := idealBranchRegister problem) branch).vec) =
      (bareState problem).vec := by
  classical
  apply WithLp.ofLp_injective
  funext label
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
  change (EuclideanSpace.projₗ (𝕜 := ℂ) label)
    (∑ branch ∈ preparedSourceBranches problem,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (R := idealBranchRegister problem) branch).vec) =
    preparedBranchAmplitude problem label
  calc
    _ = if label ∈ preparedSourceBranches problem then
        preparedBranchAmplitude problem label else 0 :=
      (coordinate (idealBranchRegister problem) (preparedSourceBranches problem)
        (preparedBranchAmplitude problem) label).trans
        (congrArg (fun decision : Decidable (label ∈ preparedSourceBranches problem) =>
          @ite ℂ _ decision (preparedBranchAmplitude problem label) 0)
          (Subsingleton.elim _ _))
    _ = _ := by
      by_cases member : label ∈ preparedSourceBranches problem
      · rw [if_pos member]
      · rw [if_neg member]
        have outside : ¬ (label.1.val < problem.order ∧ label.2.val < problem.order) := by
          intro inside
          apply member
          unfold preparedSourceBranches
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ label, inside⟩
        exact (preparedBranchAmplitude_zero problem label outside).symm

/-- Tensoring the complete original source with its arbitrary coherent reference. -/
def sourceState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (reference : NormalizedVector Reference) :
    NormalizedVector ((idealBranchRegister problem).prod Reference) :=
  NormalizedVector.prodTensor (bareState problem) reference

/-- The same original admissible source component, without conditioning or renormalization. -/
def goodVector (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector ((idealBranchRegister problem).prod Reference) :=
  HilbertVector.prodTensor
    (∑ branch ∈ preparedAdmissibleBranches problem points seed,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (R := idealBranchRegister problem) branch).vec) reference.vec

/-- Restriction to the original good branches keeps norm at most one. -/
lemma goodVector_norm_le_one (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖goodVector problem points seed reference‖ ≤ 1 := by
  classical
  rw [goodVector, HilbertVector.norm_prodTensor, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_branch_sum_le_one (R := idealBranchRegister problem)
    (preparedSourceBranches problem)
    (preparedAdmissibleBranches problem points seed) (Finset.filter_subset _ _)
    id Function.injective_id (preparedBranchAmplitude problem) (bareState problem)
    (bareState_expansion problem)

/-- No omitted branch is measured; its coherent norm is the original exceptional square root. -/
lemma norm_sourceState_sub_goodVector (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference) :
    ‖(sourceState problem reference).vec - goodVector problem points seed reference‖ =
      Real.sqrt (preparedExceptionalMass problem points seed) := by
  classical
  let good : HilbertVector (idealBranchRegister problem) :=
    ∑ branch ∈ preparedAdmissibleBranches problem points seed,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (R := idealBranchRegister problem) branch).vec
  have difference :
      HilbertVector.prodTensor (bareState problem).vec reference.vec -
          HilbertVector.prodTensor good reference.vec =
        HilbertVector.prodTensor ((bareState problem).vec - good) reference.vec := by
    apply WithLp.ofLp_injective
    funext label
    exact (sub_mul _ _ _).symm
  change ‖HilbertVector.prodTensor (bareState problem).vec reference.vec -
    HilbertVector.prodTensor good reference.vec‖ = _
  rw [difference, HilbertVector.norm_prodTensor, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_sub_branch_sum_eq_sqrt_bad (R := idealBranchRegister problem)
    (preparedSourceBranches problem)
    (preparedAdmissibleBranches problem points seed)
    (preparedExceptionalBranches problem points seed)
    (preparedBranches_partition problem points seed) (preparedBranches_disjoint problem points seed)
    id Function.injective_id (preparedBranchAmplitude problem) (bareState problem).vec
    (bareState_expansion problem)

/-- Certified effects agreeing on the good component retain the original four-square-root loss. -/
lemma effect_weight_le_add_four_sqrt (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
    {Reference : Register} (reference : NormalizedVector Reference)
    (actual ideal : Effect ((idealBranchRegister problem).prod Reference))
    (agrees : actual.weight (DensityOperator.ofSubnormalizedVector
        (goodVector problem points seed reference)
        (goodVector_norm_le_one problem points seed reference)) =
      ideal.weight (DensityOperator.ofSubnormalizedVector
        (goodVector problem points seed reference)
        (goodVector_norm_le_one problem points seed reference))) :
    ideal.weight (DensityOperator.ofPure (sourceState problem reference)) ≤
      actual.weight (DensityOperator.ofPure (sourceState problem reference)) +
        4 * Real.sqrt (preparedExceptionalMass problem points seed) := by
  have bound := Effect.weight_le_add_four_mul_omitted_norm actual ideal
    (sourceState problem reference) (goodVector problem points seed reference)
    (goodVector_norm_le_one problem points seed reference) agrees
  rw [norm_sourceState_sub_goodVector] at bound
  exact bound

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.SourceGeometry
