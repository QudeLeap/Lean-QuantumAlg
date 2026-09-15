/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Exponential remainder bounds

This file collects scalar estimates used to turn algebraic second-order
exponential remainders into norm bounds.
-/

@[expose] public section

namespace QuantumAlg

/-- For `n ≥ 2`, the reciprocal factorial is bounded by the shifted reciprocal.

This is the scalar estimate behind the index shift
`∑ n ≥ 2, x ^ n / n! ≤ (x ^ 2 / 2) * ∑ m, x ^ m / m!`.
-/
lemma factorial_inv_le_half_mul_factorial_inv (n : ℕ) (h : 2 ≤ n) :
    (1 / (Nat.factorial n : ℝ)) ≤
      (1 / 2) * (1 / (Nat.factorial (n - 2) : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hle_nat : 2 * Nat.factorial k ≤ Nat.factorial (2 + k) := by
    rw [show 2 + k = k + 2 by omega]
    rw [show k + 2 = (k + 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    have hcoeff : 2 ≤ (k + 1 + 1) * (k + 1) := by
      exact (by omega : 2 ≤ k + 1 + 1) |>.trans
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos k))
    calc
      2 * Nat.factorial k ≤ ((k + 1 + 1) * (k + 1)) * Nat.factorial k := by
        exact Nat.mul_le_mul_right _ hcoeff
      _ = (k + 1 + 1) * ((k + 1) * Nat.factorial k) := by ring
  have hle_real : (2 : ℝ) * (Nat.factorial k : ℝ) ≤
      (Nat.factorial (2 + k) : ℝ) := by
    exact_mod_cast hle_nat
  simpa using
    (calc
      (1 / (Nat.factorial (2 + k) : ℝ))
          ≤ 1 / ((2 : ℝ) * (Nat.factorial k : ℝ)) := by
        exact one_div_le_one_div_of_le (by positivity) hle_real
      _ = (1 / 2) * (1 / (Nat.factorial k : ℝ)) := by
        field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)])

/-- The tail of the real exponential series from order two is bounded by
`(x^2 / 2) * exp x` for `x ≥ 0`. -/
lemma real_exp_tail_two_le (x : ℝ) (hx : 0 ≤ x) :
    (∑' n : ℕ, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ≤
      (x ^ 2 / 2) * Real.exp x := by
  have hsx : Summable fun n : ℕ => x ^ n / (Nat.factorial n : ℝ) :=
    Real.summable_pow_div_factorial x
  have hsg : Summable fun n : ℕ =>
      (x ^ 2 / 2) * (x ^ n / (Nat.factorial n : ℝ)) :=
    hsx.mul_left _
  have hsf : Summable fun n : ℕ =>
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
    simpa [add_comm] using (summable_nat_add_iff 2).2 hsx
  have hterm : ∀ n : ℕ,
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) ≤
        (x ^ 2 / 2) * (x ^ n / (Nat.factorial n : ℝ)) := by
    intro n
    have hfac := factorial_inv_le_half_mul_factorial_inv (n + 2) (by omega)
    have hxpow : 0 ≤ x ^ (n + 2) := pow_nonneg hx _
    calc
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
          = x ^ (n + 2) * (1 / (Nat.factorial (n + 2) : ℝ)) := by
        ring
      _ ≤ x ^ (n + 2) * ((1 / 2) * (1 / (Nat.factorial n : ℝ))) := by
        simpa using mul_le_mul_of_nonneg_left hfac hxpow
      _ = (x ^ 2 / 2) * (x ^ n / (Nat.factorial n : ℝ)) := by
        rw [show n + 2 = 2 + n by omega, pow_add]
        ring
  calc
    (∑' n : ℕ, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ))
        ≤ ∑' n : ℕ, (x ^ 2 / 2) * (x ^ n / (Nat.factorial n : ℝ)) := by
      exact hsf.tsum_le_tsum hterm hsg
    _ = (x ^ 2 / 2) * Real.exp x := by
      have h_exp :
          (∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ)) = Real.exp x := by
        rw [Real.exp_eq_exp_ℝ]
        exact (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).tsum_eq
      rw [tsum_mul_left]
      rw [h_exp]

/-- A second-order upper bound for the real exponential remainder. -/
lemma real_exp_remainder_le (x : ℝ) (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ (x ^ 2 / 2) * Real.exp x := by
  let tail : ℝ := ∑' n : ℕ, x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)
  have hsx : Summable fun n : ℕ => x ^ n / (Nat.factorial n : ℝ) :=
    Real.summable_pow_div_factorial x
  have h_exp :
      (∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (x : ℝ)).tsum_eq
  have hsplit_real : Real.exp x = 1 + x + tail := by
    calc
      Real.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℝ) := h_exp.symm
      _ = (∑ n ∈ Finset.range 2, x ^ n / (Nat.factorial n : ℝ)) + tail := by
        simpa [tail] using (hsx.sum_add_tsum_nat_add 2).symm
      _ = 1 + x + tail := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
  calc
    Real.exp x - 1 - x = tail := by
      rw [hsplit_real]
      ring
    _ ≤ (x ^ 2 / 2) * Real.exp x := real_exp_tail_two_le x hx

section NormedRing

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]

/-- Each exponential-series term in a normed algebra is bounded by the
corresponding scalar exponential-series term. -/
lemma norm_exp_series_term_le [NormOneClass 𝔸] (A : 𝔸) (n : ℕ) :
    ‖((Nat.factorial n : ℚ)⁻¹) • A ^ n‖ ≤
      ‖A‖ ^ n / (Nat.factorial n : ℝ) := by
  calc
    ‖((Nat.factorial n : ℚ)⁻¹) • A ^ n‖
        ≤ ‖((Nat.factorial n : ℚ)⁻¹)‖ * ‖A ^ n‖ :=
      norm_smul_le _ _
    _ ≤ ‖((Nat.factorial n : ℚ)⁻¹)‖ * ‖A‖ ^ n := by
      exact mul_le_mul_of_nonneg_left (norm_pow_le A n) (norm_nonneg _)
    _ = ‖A‖ ^ n / (Nat.factorial n : ℝ) := by
      have hqnorm :
          ‖((Nat.factorial n : ℚ)⁻¹)‖ = ((Nat.factorial n : ℝ)⁻¹) := by
        rw [← Rat.norm_cast_real]
        norm_num [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]
      rw [hqnorm, div_eq_mul_inv]
      ring

/-- The norm of the second-order exponential remainder is bounded by the tail
of the norms of the exponential series terms. -/
lemma norm_exp_sub_one_sub_id_le_tsum_norm [CompleteSpace 𝔸] (A : 𝔸) :
    ‖NormedSpace.exp A - 1 - A‖ ≤
      ∑' n : ℕ, ‖((Nat.factorial (n + 2) : ℚ)⁻¹) • A ^ (n + 2)‖ := by
  let term : ℕ → 𝔸 := fun n => ((Nat.factorial n : ℚ)⁻¹) • A ^ n
  have hsum : Summable term := by
    simpa [term] using NormedSpace.expSeries_summable' (𝕂 := ℚ) A
  have hnorm_tail : Summable fun n : ℕ => ‖term (n + 2)‖ := by
    simpa [term] using
      (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' (𝕂 := ℚ) A)
  have h_exp : (∑' n : ℕ, term n) = NormedSpace.exp A := by
    simpa [term] using (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℚ) A).tsum_eq
  have hsplit : NormedSpace.exp A = 1 + A + ∑' n : ℕ, term (n + 2) := by
    calc
      NormedSpace.exp A = ∑' n : ℕ, term n := h_exp.symm
      _ = (∑ n ∈ Finset.range 2, term n) + ∑' n : ℕ, term (n + 2) := by
        simpa [term] using (hsum.sum_add_tsum_nat_add 2).symm
      _ = 1 + A + ∑' n : ℕ, term (n + 2) := by
        simp [term, Finset.sum_range_succ, Nat.factorial]
  calc
    ‖NormedSpace.exp A - 1 - A‖ = ‖∑' n : ℕ, term (n + 2)‖ := by
      rw [hsplit]
      have hadd :
          1 + A + (∑' n : ℕ, term (n + 2)) - 1 - A =
            ∑' n : ℕ, term (n + 2) := by
        abel
      rw [hadd]
    _ ≤ ∑' n : ℕ, ‖term (n + 2)‖ :=
      norm_tsum_le_tsum_norm hnorm_tail

/-- A second-order norm bound for the exponential in a Banach algebra. -/
theorem norm_exp_sub_one_sub_id_le [NormOneClass 𝔸] [CompleteSpace 𝔸] (A : 𝔸) :
    ‖NormedSpace.exp A - 1 - A‖ ≤
      (1 / 2) * ‖A‖ ^ 2 * Real.exp ‖A‖ := by
  have hnorm_tail : Summable fun n : ℕ =>
      ‖((Nat.factorial (n + 2) : ℚ)⁻¹) • A ^ (n + 2)‖ := by
    simpa using
      (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' (𝕂 := ℚ) A)
  have hreal_tail : Summable fun n : ℕ =>
      ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
    simpa [add_comm] using
      (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial ‖A‖)
  calc
    ‖NormedSpace.exp A - 1 - A‖
        ≤ ∑' n : ℕ, ‖((Nat.factorial (n + 2) : ℚ)⁻¹) • A ^ (n + 2)‖ :=
      norm_exp_sub_one_sub_id_le_tsum_norm A
    _ ≤ ∑' n : ℕ, ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
      exact hnorm_tail.tsum_le_tsum (fun n => norm_exp_series_term_le A (n + 2))
        hreal_tail
    _ ≤ (‖A‖ ^ 2 / 2) * Real.exp ‖A‖ :=
      real_exp_tail_two_le ‖A‖ (norm_nonneg A)
    _ = (1 / 2) * ‖A‖ ^ 2 * Real.exp ‖A‖ := by
      ring

end NormedRing

section RCLikeNormedRing

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- Each exponential-series term in a normed algebra over `ℝ` or `ℂ` is bounded
by the corresponding scalar exponential-series term. -/
lemma norm_exp_series_term_le_rclike [NormOneClass 𝔸] (A : 𝔸) (n : ℕ) :
    ‖((Nat.factorial n : 𝕂)⁻¹) • A ^ n‖ ≤
      ‖A‖ ^ n / (Nat.factorial n : ℝ) := by
  calc
    ‖((Nat.factorial n : 𝕂)⁻¹) • A ^ n‖
        ≤ ‖((Nat.factorial n : 𝕂)⁻¹)‖ * ‖A ^ n‖ :=
      norm_smul_le _ _
    _ ≤ ‖((Nat.factorial n : 𝕂)⁻¹)‖ * ‖A‖ ^ n := by
      exact mul_le_mul_of_nonneg_left (norm_pow_le A n) (norm_nonneg _)
    _ = ‖A‖ ^ n / (Nat.factorial n : ℝ) := by
      rw [norm_inv, RCLike.norm_natCast, div_eq_mul_inv]
      ring

/-- Positive exponential-series tail terms do not need a `NormOneClass`
assumption: the power is never zero. -/
lemma norm_exp_series_tail_term_le_rclike (A : 𝔸) (n : ℕ) :
    ‖((Nat.factorial (n + 2) : 𝕂)⁻¹) • A ^ (n + 2)‖ ≤
      ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
  calc
    ‖((Nat.factorial (n + 2) : 𝕂)⁻¹) • A ^ (n + 2)‖
        ≤ ‖((Nat.factorial (n + 2) : 𝕂)⁻¹)‖ * ‖A ^ (n + 2)‖ :=
      norm_smul_le _ _
    _ ≤ ‖((Nat.factorial (n + 2) : 𝕂)⁻¹)‖ * ‖A‖ ^ (n + 2) := by
      exact mul_le_mul_of_nonneg_left
        (norm_pow_le' A (by omega : 0 < n + 2)) (norm_nonneg _)
    _ = ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
      rw [norm_inv, RCLike.norm_natCast, div_eq_mul_inv]
      ring

/-- The norm of the second-order exponential remainder is bounded by the tail
of the norms of the exponential series terms over `ℝ` or `ℂ`. -/
lemma norm_exp_sub_one_sub_id_le_tsum_norm_rclike [CompleteSpace 𝔸] (A : 𝔸) :
    ‖NormedSpace.exp A - 1 - A‖ ≤
      ∑' n : ℕ, ‖((Nat.factorial (n + 2) : 𝕂)⁻¹) • A ^ (n + 2)‖ := by
  let term : ℕ → 𝔸 := fun n => ((Nat.factorial n : 𝕂)⁻¹) • A ^ n
  have hsum : Summable term := by
    simpa [term] using NormedSpace.expSeries_summable' (𝕂 := 𝕂) A
  have hnorm_tail : Summable fun n : ℕ => ‖term (n + 2)‖ := by
    simpa [term] using
      (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' (𝕂 := 𝕂) A)
  have h_exp : (∑' n : ℕ, term n) = NormedSpace.exp A := by
    simpa [term] using (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) A).tsum_eq
  have hsplit : NormedSpace.exp A = 1 + A + ∑' n : ℕ, term (n + 2) := by
    calc
      NormedSpace.exp A = ∑' n : ℕ, term n := h_exp.symm
      _ = (∑ n ∈ Finset.range 2, term n) + ∑' n : ℕ, term (n + 2) := by
        simpa [term] using (hsum.sum_add_tsum_nat_add 2).symm
      _ = 1 + A + ∑' n : ℕ, term (n + 2) := by
        simp [term, Finset.sum_range_succ, Nat.factorial]
  calc
    ‖NormedSpace.exp A - 1 - A‖ = ‖∑' n : ℕ, term (n + 2)‖ := by
      rw [hsplit]
      have hadd :
          1 + A + (∑' n : ℕ, term (n + 2)) - 1 - A =
            ∑' n : ℕ, term (n + 2) := by
        abel
      rw [hadd]
    _ ≤ ∑' n : ℕ, ‖term (n + 2)‖ :=
      norm_tsum_le_tsum_norm hnorm_tail

/-- A second-order norm bound for the exponential in a Banach algebra over
`ℝ` or `ℂ`. -/
theorem norm_exp_sub_one_sub_id_le_rclike (𝕂 : Type*) [RCLike 𝕂]
    [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] (A : 𝔸) :
    ‖NormedSpace.exp A - 1 - A‖ ≤
      (1 / 2) * ‖A‖ ^ 2 * Real.exp ‖A‖ := by
  have hnorm_tail : Summable fun n : ℕ =>
      ‖((Nat.factorial (n + 2) : 𝕂)⁻¹) • A ^ (n + 2)‖ := by
    simpa using
      (summable_nat_add_iff 2).2 (NormedSpace.norm_expSeries_summable' (𝕂 := 𝕂) A)
  have hreal_tail : Summable fun n : ℕ =>
      ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
    simpa [add_comm] using
      (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial ‖A‖)
  calc
    ‖NormedSpace.exp A - 1 - A‖
        ≤ ∑' n : ℕ, ‖((Nat.factorial (n + 2) : 𝕂)⁻¹) • A ^ (n + 2)‖ :=
      norm_exp_sub_one_sub_id_le_tsum_norm_rclike A
    _ ≤ ∑' n : ℕ, ‖A‖ ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) := by
      exact hnorm_tail.tsum_le_tsum
        (fun n => norm_exp_series_tail_term_le_rclike (𝕂 := 𝕂) A n)
        hreal_tail
    _ ≤ (‖A‖ ^ 2 / 2) * Real.exp ‖A‖ :=
      real_exp_tail_two_le ‖A‖ (norm_nonneg A)
    _ = (1 / 2) * ‖A‖ ^ 2 * Real.exp ‖A‖ := by
      ring

end RCLikeNormedRing

/-- The concrete complex norm satisfies the scalar-square hypothesis used in
the global qDRIFT bound. -/
theorem complex_norm_scalar_square_bound (t : ℝ) (steps : ℕ) :
    (‖(((t / (steps : ℝ) : ℝ) : ℂ) ^ 2)‖ : ℝ)
      ≤ (t / (steps : ℝ)) ^ 2 := by
  rw [norm_pow]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.norm_div,
    Complex.norm_real, Real.norm_eq_abs, RCLike.norm_natCast]
  rw [div_pow, div_pow, sq_abs]

/-- Mathlib's complex exponential second-order remainder estimate, re-exported
in the shape used by the qDRIFT scalar remainder interface. -/
theorem complex_exp_second_order_remainder_bound (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 :=
  Complex.norm_exp_sub_one_sub_id_le hz

/-- Complex exponential second-order remainder bound with the global
`exp ‖z‖` tail factor. -/
theorem complex_exp_second_order_remainder_bound_exp (z : ℂ) :
    ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ := by
  calc
    ‖Complex.exp z - 1 - z‖
        = ‖Complex.exp z - ∑ m ∈ Finset.range 2, z ^ m / m.factorial‖ := by
      simp [sub_eq_add_neg, Finset.sum_range_succ_comm, add_assoc, Nat.factorial]
    _ ≤ ‖z‖ ^ 2 * Real.exp ‖z‖ :=
      Complex.norm_exp_sub_sum_le_norm_mul_exp z 2

end QuantumAlg
