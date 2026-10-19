/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation.State
import all QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Original prepared source range, good/bad partition and exact exceptional mass

This canonical mathematical owner retains the original declaration names and bodies. It has no
physical input, old execution, prepared-state compiler, channel comparison or
new success-floor theorem. The original range and two-value admissibility
predicate are retained; the good component is not renormalized.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open QuantumAlg QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

universe u

/-- The original two independent exact range preparations give this complex product amplitude. -/
def preparedBranchAmplitude {G : Type u} [Group G]
    (problem : FiniteCyclicDLP.KnownOrderProblem G)
    (branch : Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) : ℂ :=
  FiniteCyclicDLP.Concrete.BornBridge.exponentState problem branch.1 *
    FiniteCyclicDLP.Concrete.BornBridge.exponentState problem branch.2

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Exact support of the original two range-uniform exponent preparations. -/
def preparedSourceBranches (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E)) :
    Finset (Fin (2 ^ FiniteCyclicDLP.orderWidth problem) ×
      Fin (2 ^ FiniteCyclicDLP.orderWidth problem)) := by
  classical
  exact Finset.univ.filter fun branch =>
    branch.1.val < problem.order ∧ branch.2.val < problem.order

/-- The original range preparation contains exactly the original order-squared branch count. -/
lemma preparedSourceBranches_card
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
lemma preparedBranchAmplitude_norm_sq
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
lemma preparedExceptionalMass_eq_card_mul_inv_sq
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
lemma preparedBranches_partition (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
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
lemma preparedBranches_disjoint (problem : FiniteCyclicDLP.KnownOrderProblem (GroupPoint E))
    (points : Fin (2 * FiniteCyclicDLP.orderWidth problem) → AffinePoint E)
    (seed : AffinePoint E) : Disjoint (preparedAdmissibleBranches problem points seed)
      (preparedExceptionalBranches problem points seed) := by
  classical
  rw [Finset.disjoint_left]
  intro branch good bad
  exact (Finset.mem_filter.mp bad).2 (Finset.mem_filter.mp good).2

private lemma preparedBranchAmplitude_zero
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

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
