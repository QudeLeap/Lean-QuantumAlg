/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support.Preparation
import all QuantumAlg.Core.Base.State.Density.Vector

/-!
# Original prepared admissible support on the actual Montgomery input

The original source-range amplitudes are restricted by the original group
`Admissible` predicate. Every selected step avoids the two original exceptional
values. The omitted norm is the square root of that exact exceptional mass;
no stricter RNSL denominator domain is substituted for the original domain.
The full reference remains coherent, and the good vector is never renormalized.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation
open ScalarMultiplication.MeasuredPlacement.Encoding

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Exact support of the original two range-uniform exponent preparations. -/
def preparedSourceBranches (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) :
    Finset (Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) := by
  classical
  exact Finset.univ.filter fun branch =>
    branch.1.val < problem.order ∧ branch.2.val < problem.order

/-- The original range preparation contains exactly the original order-squared branch count. -/
theorem preparedSourceBranches_card
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) :
    (preparedSourceBranches problem).card = problem.order * problem.order := by
  classical
  let sourceRange : Finset (Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) :=
    Finset.univ.filter fun index => index.val < problem.order
  have sourceRangeFits : problem.order ≤ 2 ^ FiniteCyclicDLP.orderWidth problem :=
    FiniteCyclicDLP.order_le_fourierModulus problem
  have sourceRangeCard : sourceRange.card = problem.order := by
    dsimp only [sourceRange]
    rw [Fin.card_filter_val_lt, min_eq_right sourceRangeFits]
  have supportEq : preparedSourceBranches problem = sourceRange ×ˢ sourceRange := by
    ext branch
    simp [preparedSourceBranches, sourceRange]
  rw [supportEq, Finset.card_product, sourceRangeCard]

/-- Original group-admissible branches inside the exact source-range support. -/
def preparedAdmissibleBranches (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) :
    Finset (Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) := by
  classical
  exact (preparedSourceBranches problem).filter
    (ExceptionalOffsetAveraging.Admissible (2 * FiniteCyclicDLP.orderWidth problem)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected (FiniteCyclicDLP.orderWidth problem))
      (fun index => (points index).toGroupPoint) seed.toGroupPoint)

/-- Exceptional branches use the original two-value domain and the original prepared range. -/
def preparedExceptionalBranches (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) :
    Finset (Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) :=
  ExceptionalOffsetAveraging.badBranches (preparedSourceBranches problem)
    (2 * FiniteCyclicDLP.orderWidth problem)
    (ExceptionalOffsetAveraging.pairedBigEndianSelected (FiniteCyclicDLP.orderWidth problem))
    (fun index => (points index).toGroupPoint) seed.toGroupPoint

/-- The original exceptional Born mass is the sum of the original complex-amplitude squares. -/
def preparedExceptionalMass (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) : ℝ :=
  ∑ branch ∈ preparedExceptionalBranches problem points seed,
    ‖preparedBranchAmplitude problem branch‖ ^ 2

/-- Every supported branch keeps exactly the original reciprocal-square Born weight. -/
theorem preparedBranchAmplitude_norm_sq
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem))
    (member : branch ∈ preparedSourceBranches problem) :
    ‖preparedBranchAmplitude problem branch‖ ^ 2 =
      ((problem.order : ℝ)⁻¹) * ((problem.order : ℝ)⁻¹) := by
  classical
  have inRange := (Finset.mem_filter.mp member).2
  simp only [preparedBranchAmplitude,
    FiniteCyclicDLP.Concrete.BornBridge.exponentState_apply,
    if_pos inRange.1, if_pos inRange.2, norm_mul, mul_pow,
    FiniteCyclicDLP.norm_sq_invSqrtOrder problem.order_pos]

/-- The original exceptional mass is exactly the bad-branch count times the original weight. -/
theorem preparedExceptionalMass_eq_card_mul_inv_sq
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) :
    preparedExceptionalMass problem points seed =
      (preparedExceptionalBranches problem points seed).card *
        (((problem.order : ℝ)⁻¹) * ((problem.order : ℝ)⁻¹)) := by
  classical
  unfold preparedExceptionalMass
  calc
    (∑ branch ∈ preparedExceptionalBranches problem points seed,
      ‖preparedBranchAmplitude problem branch‖ ^ 2) =
      ∑ _branch ∈ preparedExceptionalBranches problem points seed,
        ((problem.order : ℝ)⁻¹) * ((problem.order : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro branch member
          exact preparedBranchAmplitude_norm_sq problem branch (Finset.mem_filter.mp member).1
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The two original filters partition exactly the prepared source range. -/
theorem preparedBranches_partition (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) :
    preparedAdmissibleBranches problem points seed ∪
      preparedExceptionalBranches problem points seed = preparedSourceBranches problem := by
  classical
  ext branch
  simp only [preparedAdmissibleBranches, preparedExceptionalBranches,
    ExceptionalOffsetAveraging.badBranches, Finset.mem_union, Finset.mem_filter]
  tauto

/-- No branch belongs to both the original good and exceptional filters. -/
theorem preparedBranches_disjoint (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) : Disjoint (preparedAdmissibleBranches problem points seed)
      (preparedExceptionalBranches problem points seed) := by
  classical
  rw [Finset.disjoint_left]
  intro branch good bad
  exact (Finset.mem_filter.mp bad).2 (Finset.mem_filter.mp good).2

private theorem preparedBranchAmplitude_zero
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem))
    (outside : ¬ (branch.1.val < problem.order ∧ branch.2.val < problem.order)) :
    preparedBranchAmplitude problem branch = 0 := by
  classical
  simp only [preparedBranchAmplitude, FiniteCyclicDLP.Concrete.BornBridge.exponentState_apply]
  by_cases left : branch.1.val < problem.order
  · have right : ¬branch.2.val < problem.order := fun member => outside ⟨left, member⟩
    simp [left, right]
  · simp [left]

variable [Fact p.Prime]

/-- Restricting to the original prepared range removes only exactly zero-amplitude terms. -/
theorem preparedMontgomery_source_expansion
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) :
    (∑ branch ∈ preparedSourceBranches problem,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (pairedMontgomeryInput fieldTail
          (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch) :
          HilbertVector (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register)) =
      ∑ branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
        Fin (2 ^ FiniteCyclicDLP.orderWidth problem),
        preparedBranchAmplitude problem branch •
          (NormalizedVector.ket (pairedMontgomeryInput fieldTail
            (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch) :
            HilbertVector (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register) := by
  classical
  rw [preparedSourceBranches, Finset.sum_filter_of_ne]
  intro branch _ nonzero
  by_contra outside
  apply nonzero
  rw [preparedBranchAmplitude_zero problem branch outside, zero_smul]

/-- The original good component retains all original amplitudes and the full reference. -/
def preparedGoodVector (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    HilbertVector (Register.prod
      (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register Reference) :=
  referenceFrame (∑ branch ∈ preparedAdmissibleBranches problem points seed,
    preparedBranchAmplitude problem branch •
      (NormalizedVector.ket (pairedMontgomeryInput fieldTail
        (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch) :
        HilbertVector (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register))
    reference.vec

private theorem preparedBare_expansion
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (seed : AffinePoint E) :
    (∑ branch ∈ preparedSourceBranches problem,
      preparedBranchAmplitude problem branch •
        (NormalizedVector.ket (pairedMontgomeryInput fieldTail
          (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch) :
          HilbertVector (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register)) =
      (preparedInputVector p problem
        (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
          (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
            (Fact.out : Nat.Prime p).pos fits seed.x))
        (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
          (GenericPointAddition.InPlace.Semantics.montgomeryWord fieldTail p
            (Fact.out : Nat.Prime p).pos fits seed.y))).vec := by
  rw [preparedMontgomery_source_expansion]
  unfold pairedMontgomeryInput montgomeryInput
  exact preparedInputVector_expansion _ _ _ _

/-- The coherent original good component is subnormalized without any branch conditioning. -/
theorem preparedGoodVector_norm_le_one
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    ‖preparedGoodVector problem fieldTail sameWidth fits points seed reference‖ ≤ 1 := by
  classical
  rw [preparedGoodVector, referenceFrame_norm, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_branch_sum_le_one (preparedSourceBranches problem)
    (preparedAdmissibleBranches problem points seed) (Finset.filter_subset _ _)
    _ (pairedMontgomeryInput_injective fieldTail _ sameWidth fits seed)
    (preparedBranchAmplitude problem) _
    (preparedBare_expansion problem fieldTail sameWidth fits seed)

/-- The omitted coherent norm is exactly the square root of the original exceptional mass. -/
theorem norm_preparedMontgomery_sub_good
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    ‖(preparedMontgomeryVector problem fieldTail sameWidth fits seed reference).vec -
      preparedGoodVector problem fieldTail sameWidth fits points seed reference‖ =
      Real.sqrt (preparedExceptionalMass problem points seed) := by
  classical
  change ‖referenceFrame _ reference.vec - referenceFrame _ reference.vec‖ = _
  rw [← referenceFrame_sub, referenceFrame_norm, reference.norm_eq_one, mul_one]
  exact HilbertVector.norm_sub_branch_sum_eq_sqrt_bad (preparedSourceBranches problem)
    (preparedAdmissibleBranches problem points seed)
    (preparedExceptionalBranches problem points seed)
    (preparedBranches_partition problem points seed) (preparedBranches_disjoint problem points seed)
    _ (pairedMontgomeryInput_injective fieldTail _ sameWidth fits seed)
    (preparedBranchAmplitude problem) _
    (preparedBare_expansion problem fieldTail sameWidth fits seed)

/-- The unnormalized coherent good vector lies on the original actual scalar input domain. -/
theorem preparedGoodVector_supported
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference)
    (label : (Register.prod
      (before p.size (2 * FiniteCyclicDLP.orderWidth problem)).register Reference).Index)
    (outside : ¬pairedMontgomeryAllowed E fieldTail sameWidth fits points seed label.1) :
    preparedGoodVector problem fieldTail sameWidth fits points seed reference label = 0 := by
  classical
  apply referenceFrame_zero
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro branch good
  have different : label.1 ≠ pairedMontgomeryInput fieldTail
      (FiniteCyclicDLP.orderWidth problem) sameWidth fits seed branch := by
    intro same
    exact outside ⟨branch, same, (Finset.mem_filter.mp good).2⟩
  rw [NormalizedVector.ket_apply, if_neg different, mul_zero]

/-- The exact rank-one good density satisfies the scalar theorem's complete diagonal support. -/
theorem preparedGoodDensity_supported
    (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) {Reference : Register} (reference : NormalizedVector Reference) :
    ∀ label, ¬pairedMontgomeryAllowed E fieldTail sameWidth fits points seed label.1 →
      (DensityOperator.ofSubnormalizedVector
        (preparedGoodVector problem fieldTail sameWidth fits points seed reference)
        (preparedGoodVector_norm_le_one problem fieldTail sameWidth fits
          points seed reference)).matrix
          label label = 0 :=
  DensityOperator.ofSubnormalizedVector_supported _ _ _
    (preparedGoodVector_supported problem fieldTail sameWidth fits points seed reference)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
