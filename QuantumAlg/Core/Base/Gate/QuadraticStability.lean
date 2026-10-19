/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Basic

/-!
# Coherent support comparisons for contractive quadratic forms

A contractive matrix has a quadratic form whose change is controlled by the
input-vector distance. Two such forms agreeing on the complete coherent good
component therefore differ by at most four times the omitted component norm.
Contractivity and coherent agreement are explicit premises. No execution
instruction, measurement effect or channel representation is inferred here.
-/

namespace QuantumAlg.HilbertOperator

noncomputable section

/-- Real quadratic weight of an unrestricted matrix on a raw finite-register vector. -/
def quadraticWeight {R : Register} (operator : HilbertOperator R) (vector : HilbertVector R) :
    ℝ := (inner ℂ vector (operator.applyVec vector)).re

/-- A contractive matrix has a dimension-independent quadratic continuity bound. -/
lemma quadraticWeight_sub_bound {R : Register} (operator : HilbertOperator R)
    (contractive : ∀ vector : HilbertVector R, ‖operator.applyVec vector‖ ≤ ‖vector‖)
    (left right : HilbertVector R) :
    |quadraticWeight operator left - quadraticWeight operator right| ≤
      ‖left - right‖ * (‖left‖ + ‖right‖) := by
  have difference : quadraticWeight operator left - quadraticWeight operator right =
      (inner ℂ (left - right) (operator.applyVec left)).re +
        (inner ℂ right (operator.applyVec (left - right))).re := by
    rw [applyVec_sub, inner_sub_left, inner_sub_right]
    simp only [quadraticWeight, Complex.sub_re]
    ring
  rw [difference]
  calc
    _ ≤ |(inner ℂ (left - right) (operator.applyVec left)).re| +
        |(inner ℂ right (operator.applyVec (left - right))).re| := abs_add_le _ _
    _ ≤ ‖inner ℂ (left - right) (operator.applyVec left)‖ +
        ‖inner ℂ right (operator.applyVec (left - right))‖ :=
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
    _ ≤ ‖left - right‖ * ‖operator.applyVec left‖ +
        ‖right‖ * ‖operator.applyVec (left - right)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖left - right‖ * ‖left‖ + ‖right‖ * ‖left - right‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (contractive left) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (contractive (left - right)) (norm_nonneg _))
    _ = ‖left - right‖ * (‖left‖ + ‖right‖) := by ring

/-- Agreement on the full coherent good vector gives the original four-times-norm error. -/
lemma quadraticWeight_le_add_four_mul_norm_sub {R : Register}
    (actual ideal : HilbertOperator R)
    (actualContractive : ∀ vector : HilbertVector R, ‖actual.applyVec vector‖ ≤ ‖vector‖)
    (idealContractive : ∀ vector : HilbertVector R, ‖ideal.applyVec vector‖ ≤ ‖vector‖)
    (input : NormalizedVector R) (good : HilbertVector R) (goodNorm : ‖good‖ ≤ 1)
    (agrees : quadraticWeight actual good = quadraticWeight ideal good) :
    quadraticWeight ideal input ≤ quadraticWeight actual input +
      4 * ‖(input : HilbertVector R) - good‖ := by
  have factor : ‖(input : HilbertVector R) - good‖ *
      (‖(input : HilbertVector R)‖ + ‖good‖) ≤
        2 * ‖(input : HilbertVector R) - good‖ := by
    rw [input.norm_eq_one]
    nlinarith [norm_nonneg ((input : HilbertVector R) - good)]
  have idealBound := (quadraticWeight_sub_bound ideal idealContractive input good).trans factor
  have actualBound := (quadraticWeight_sub_bound actual actualContractive input good).trans factor
  have idealUpper := (abs_le.mp idealBound).2
  have actualLower := (abs_le.mp actualBound).1
  linarith

end

end QuantumAlg.HilbertOperator
