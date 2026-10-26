/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.OperatorNorm
import Mathlib.Tactic

/-!
# Local commutator bounds for operator products

The commutator is a derivation. Bounds on its first two applications to the
individual factors therefore give a quadratic, rather than exponential,
dependence on the number of factors. This supplies the local algebra behind
nested-commutator product-formula bounds [CST+21, prefactor.tex:105-114].
-/

@[expose] public section

namespace QuantumAlg.Trotter

open HilbertOperator

noncomputable section

variable {R : Register}

private lemma lie_product_rule (K A B : HilbertOperator R) :
    ⁅K, A * B⁆ = ⁅K, A⁆ * B + A * ⁅K, B⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

private lemma lie_product_rule_twice (K A B : HilbertOperator R) :
    ⁅K, ⁅K, A * B⁆⁆ =
      ⁅K, ⁅K, A⁆⁆ * B + ⁅K, A⁆ * ⁅K, B⁆ +
        ⁅K, A⁆ * ⁅K, B⁆ + A * ⁅K, ⁅K, B⁆⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- A list of contractions, each with first derivative at most `a` and
second derivative at most `a²`, has the corresponding length and length-squared
commutator bounds. No commutation between the factors is assumed. -/
lemma commutator_list_prod_bounds [Nonempty R.Index]
    (K : HilbertOperator R) (a : ℝ) (ha : 0 ≤ a)
    (xs : List (HilbertOperator R))
    (hxs : ∀ X ∈ xs,
      opNorm X ≤ 1 ∧ opNorm ⁅K, X⁆ ≤ a ∧ opNorm ⁅K, ⁅K, X⁆⁆ ≤ a ^ 2) :
    opNorm xs.prod ≤ 1 ∧
      opNorm ⁅K, xs.prod⁆ ≤ (xs.length : ℝ) * a ∧
      opNorm ⁅K, ⁅K, xs.prod⁆⁆ ≤ (xs.length : ℝ) ^ 2 * a ^ 2 := by
  induction xs with
  | nil =>
      simp only [List.prod_nil, List.length_nil, Nat.cast_zero, zero_mul, zero_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, opNorm_one, le_refl, true_and]
      simp [Ring.lie_def]
  | cons X xs ih =>
      obtain ⟨hX, hX₁, hX₂⟩ := hxs X (by simp)
      obtain ⟨hp, hp₁, hp₂⟩ := ih (fun Y hY => hxs Y (by simp [hY]))
      simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      refine ⟨?_, ?_, ?_⟩
      · calc
          opNorm (X * xs.prod) ≤ opNorm X * opNorm xs.prod := opNorm_mul_le _ _
          _ ≤ 1 * 1 := mul_le_mul hX hp (opNorm_nonneg _) (by norm_num)
          _ = 1 := by norm_num
      · rw [lie_product_rule]
        calc
          _ ≤ opNorm (⁅K, X⁆ * xs.prod) + opNorm (X * ⁅K, xs.prod⁆) :=
            opNorm_add_le _ _
          _ ≤ opNorm ⁅K, X⁆ * opNorm xs.prod + opNorm X * opNorm ⁅K, xs.prod⁆ :=
            add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
          _ ≤ a * 1 + 1 * ((xs.length : ℝ) * a) := by
            gcongr <;> exact opNorm_nonneg _
          _ = ((xs.length : ℝ) + 1) * a := by ring
      · rw [lie_product_rule_twice]
        calc
          _ ≤ opNorm (⁅K, ⁅K, X⁆⁆ * xs.prod + ⁅K, X⁆ * ⁅K, xs.prod⁆ +
              ⁅K, X⁆ * ⁅K, xs.prod⁆) + opNorm (X * ⁅K, ⁅K, xs.prod⁆⁆) :=
            opNorm_add_le _ _
          _ ≤ (opNorm (⁅K, ⁅K, X⁆⁆ * xs.prod + ⁅K, X⁆ * ⁅K, xs.prod⁆) +
              opNorm (⁅K, X⁆ * ⁅K, xs.prod⁆)) +
              opNorm (X * ⁅K, ⁅K, xs.prod⁆⁆) := by
            gcongr
            exact opNorm_add_le _ _
          _ ≤ ((opNorm (⁅K, ⁅K, X⁆⁆ * xs.prod) +
              opNorm (⁅K, X⁆ * ⁅K, xs.prod⁆)) +
              opNorm (⁅K, X⁆ * ⁅K, xs.prod⁆)) +
              opNorm (X * ⁅K, ⁅K, xs.prod⁆⁆) := by
            gcongr
            exact opNorm_add_le _ _
          _ ≤ ((opNorm ⁅K, ⁅K, X⁆⁆ * opNorm xs.prod +
              opNorm ⁅K, X⁆ * opNorm ⁅K, xs.prod⁆) +
              opNorm ⁅K, X⁆ * opNorm ⁅K, xs.prod⁆) +
              opNorm X * opNorm ⁅K, ⁅K, xs.prod⁆⁆ := by
            gcongr <;> exact opNorm_mul_le _ _
          _ ≤ ((a ^ 2 * 1 + a * ((xs.length : ℝ) * a)) +
              a * ((xs.length : ℝ) * a)) +
              1 * ((xs.length : ℝ) ^ 2 * a ^ 2) := by
            gcongr <;> exact opNorm_nonneg _
          _ = ((xs.length : ℝ) + 1) ^ 2 * a ^ 2 := by ring

end

end QuantumAlg.Trotter
