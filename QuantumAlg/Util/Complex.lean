/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Complex exponential and unit-circle helper lemmas (quantum-free)

Generic identities used by the QSP development, factored out so they carry no
dependency on the quantum framework (gates, states): phase-factor scalars
`e^{±iφ}`, the special values `e^{±iπ/2}`, `e^{±iπ/4}`, the real-square-root
identity `√(1-x²)² = 1-x²`, injectivity of `t ↦ e^{it}` on `(0, π)`, and the
SU(2)/unit-circle parameterizations (`mul_conj_eq_norm_sq`, `exists_unit_mul`,
`exists_real_unit`, `exists_cos_sin`, `exists_exp_sq_eq`).

These are upstream candidates for Mathlib; nothing here mentions `Gate`/`PureState`.
-/

@[expose] public section

namespace QuantumAlg

open Complex

/-- `exp(iθ) = cos θ + i sin θ` for real `θ`, with real-valued `cos/sin`. -/
theorem exp_ofReal_mul_I (θ : ℝ) :
    Complex.exp (θ * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

theorem conj_exp_I (φ : ℝ) :
    starRingEnd ℂ (Complex.exp (φ * Complex.I)) =
      Complex.exp (-(φ * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem conj_exp_neg_I (φ : ℝ) :
    starRingEnd ℂ (Complex.exp (-(φ * Complex.I))) =
      Complex.exp (φ * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem exp_I_mul_exp_neg_I (φ : ℝ) :
    Complex.exp (φ * Complex.I) * Complex.exp (-(φ * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem exp_neg_I_mul_exp_I (φ : ℝ) :
    Complex.exp (-(φ * Complex.I)) * Complex.exp (φ * Complex.I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- Multiplying two unit-circle exponentials subtracts their real phases in the
exponent. This is the scalar algebra used by phase-register geometric sums. -/
private theorem exp_neg_two_pi_mul_mul_exp_two_pi_mul (a b k : ℝ) :
    Complex.exp (-(2 * Real.pi * b * k) * Complex.I) *
        Complex.exp (2 * Real.pi * a * k * Complex.I) =
      Complex.exp (2 * Real.pi * ((a - b) * k) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- A finite exponential phase progression is a geometric progression on the
unit-circle base. -/
theorem sum_range_exp_two_pi_mul_nat_mul_I_eq_geom (θ : ℝ) (m : ℕ) :
    (Finset.range m).sum
        (fun b => Complex.exp (2 * Real.pi *
          (((b : ℝ) * θ : ℝ) : ℂ) * Complex.I)) =
      (Finset.range m).sum
        (fun b => Complex.exp (2 * Real.pi * θ * Complex.I) ^ b) := by
  refine Finset.sum_congr rfl fun b _hb => ?_
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Degenerate finite exponential progression when the unit-circle base is
one. -/
theorem sum_range_exp_two_pi_mul_nat_mul_I_eq_natCast_of_base_eq_one
    {θ : ℝ} {m : ℕ}
    (hbase : Complex.exp (2 * Real.pi * θ * Complex.I) = 1) :
    (Finset.range m).sum
        (fun b => Complex.exp (2 * Real.pi *
          (((b : ℝ) * θ : ℝ) : ℂ) * Complex.I)) =
      (m : ℂ) := by
  rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_geom]
  simp [hbase]

/-- Closed form for a finite exponential phase progression with nontrivial
unit-circle base. -/
theorem sum_range_exp_two_pi_mul_nat_mul_I_eq_geom_closed
    {θ : ℝ} {m : ℕ}
    (hne : Complex.exp (2 * Real.pi * θ * Complex.I) ≠ 1) :
    (Finset.range m).sum
        (fun b => Complex.exp (2 * Real.pi *
          (((b : ℝ) * θ : ℝ) : ℂ) * Complex.I)) =
      (Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1) /
        (Complex.exp (2 * Real.pi * θ * Complex.I) - 1) := by
  rw [sum_range_exp_two_pi_mul_nat_mul_I_eq_geom]
  exact geom_sum_eq hne m

/-- Unit-circle chord upper bound in the `x * I` convention used by the local
phase formulas. -/
theorem norm_exp_ofReal_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - 1‖ ≤ |x| := by
  simpa [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x))

/-- Unit-circle chord lower bound in the `I * x` convention, valid on one
principal interval. -/
theorem two_div_pi_mul_abs_le_norm_exp_I_mul_ofReal_sub_one
    {x : ℝ} (hx : |x| ≤ Real.pi) :
    (2 / Real.pi) * |x| ≤
      ‖Complex.exp (Complex.I * x) - 1‖ := by
  have hnorm :
      ‖Complex.exp (Complex.I * x) - 1‖ =
        2 * |Real.sin (x / 2)| := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    simp
  rw [hnorm]
  have hxhalf : |x / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hxhalf
  calc
    (2 / Real.pi) * |x| =
        2 * ((2 / Real.pi) * |x / 2|) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ 2 * |Real.sin (x / 2)| := by
      nlinarith

/-- Unit-circle chord lower bound in the `x * I` convention used by the local
phase formulas. -/
theorem two_div_pi_mul_abs_le_norm_exp_ofReal_mul_I_sub_one
    {x : ℝ} (hx : |x| ≤ Real.pi) :
    (2 / Real.pi) * |x| ≤
      ‖Complex.exp (x * Complex.I) - 1‖ := by
  simpa [mul_comm] using
    (two_div_pi_mul_abs_le_norm_exp_I_mul_ofReal_sub_one (x := x) hx)

/-- Denominator bound for the `2πθ` unit-circle base. -/
theorem norm_exp_two_pi_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ ≤
      |2 * Real.pi * θ| := by
  convert norm_exp_ofReal_mul_I_sub_one_le (2 * Real.pi * θ) using 2
  push_cast
  ring

/-- Numerator lower bound for a finite `2πθ` geometric phase on the principal
interval. -/
theorem two_div_pi_mul_abs_le_norm_exp_two_pi_mul_nat_mul_I_sub_one
    {θ : ℝ} {m : ℕ}
    (hprincipal : |2 * Real.pi * ((m : ℝ) * θ)| ≤ Real.pi) :
    (2 / Real.pi) * |2 * Real.pi * ((m : ℝ) * θ)| ≤
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ := by
  rw [← Complex.exp_nat_mul]
  have harg :
      (m : ℂ) * (2 * Real.pi * θ * Complex.I) =
        2 * Real.pi * (((m : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  convert two_div_pi_mul_abs_le_norm_exp_ofReal_mul_I_sub_one
    (x := 2 * Real.pi * ((m : ℝ) * θ)) hprincipal using 2
  push_cast
  ring

/-- Concavity of sine gives the secant-line lower bound from `0` to `A` on
`[0, π]`. -/
theorem sin_ge_slope_mul_of_nonneg_of_le
    {x A : ℝ} (hApos : 0 < A) (hApi : A ≤ Real.pi)
    (hx0 : 0 ≤ x) (hxA : x ≤ A) :
    (Real.sin A / A) * x ≤ Real.sin x := by
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hscale0 : 0 ≤ x / A := div_nonneg hx0 hApos.le
  have hscale1 : x / A ≤ 1 := by
    rw [div_le_one hApos]
    exact hxA
  have hconc :=
    strictConcaveOn_sin_Icc.concaveOn.2
      ⟨le_rfl, Real.pi_pos.le⟩ ⟨hApos.le, hApi⟩
      (sub_nonneg.2 hscale1) hscale0
  simpa [mul_comm x, div_eq_mul_inv, mul_assoc, mul_left_comm, hA0] using hconc

/-- Numerator lower bound for a finite `2πθ` geometric phase from an explicit
absolute phase-angle bound. -/
theorem norm_exp_two_pi_mul_nat_mul_I_sub_one_lower_bound_of_angle_le
    {θ A : ℝ} {m : ℕ}
    (hApos : 0 < A) (hApi : A ≤ Real.pi)
    (hangle : Real.pi * ((m : ℝ) * |θ|) ≤ A) :
    2 * ((Real.sin A / A) * (Real.pi * ((m : ℝ) * |θ|))) ≤
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ := by
  let x : ℝ := Real.pi * ((m : ℝ) * |θ|)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxA : x ≤ A := by
    simpa [x] using hangle
  have hxpi : x ≤ Real.pi := le_trans hxA hApi
  have harg_abs :
      |Real.pi * ((m : ℝ) * θ)| = x := by
    dsimp [x]
    rw [abs_mul, abs_mul, abs_of_nonneg Real.pi_pos.le,
      abs_of_nonneg (Nat.cast_nonneg m)]
  have hnorm :
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ =
        2 * |Real.sin (Real.pi * ((m : ℝ) * θ))| := by
    rw [← Complex.exp_nat_mul]
    have harg :
        (m : ℂ) * (2 * Real.pi * θ * Complex.I) =
          (2 * Real.pi * (((m : ℝ) * θ : ℝ) : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [harg]
    have hcomm :
        (2 * Real.pi * (((m : ℝ) * θ : ℝ) : ℂ)) * Complex.I =
          Complex.I * ((2 * Real.pi * ((m : ℝ) * θ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcomm, Complex.norm_exp_I_mul_ofReal_sub_one]
    simp [Real.norm_eq_abs]
    ring_nf
  rw [hnorm]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
    rw [harg_abs]
    exact hxpi)]
  rw [harg_abs]
  have hsin := sin_ge_slope_mul_of_nonneg_of_le hApos hApi hx0 hxA
  nlinarith

/-- Lower bound for the norm quotient of a nontrivial finite unit-circle
geometric phase. -/
theorem geometric_phase_norm_ratio_lower_bound
    {θ : ℝ} {m : ℕ}
    (hprincipal : |2 * Real.pi * ((m : ℝ) * θ)| ≤ Real.pi)
    (hne : Complex.exp (2 * Real.pi * θ * Complex.I) ≠ 1) :
    ((2 / Real.pi) * |2 * Real.pi * ((m : ℝ) * θ)|) /
        |2 * Real.pi * θ| ≤
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ /
        ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ := by
  have hnum :
      (2 / Real.pi) * |2 * Real.pi * ((m : ℝ) * θ)| ≤
        ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ :=
    two_div_pi_mul_abs_le_norm_exp_two_pi_mul_nat_mul_I_sub_one hprincipal
  have hden :
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ ≤
        |2 * Real.pi * θ| :=
    norm_exp_two_pi_mul_I_sub_one_le θ
  have hden_pos :
      0 < ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  exact div_le_div₀ (norm_nonneg _) hnum hden_pos hden

/-- Lower bound for the norm quotient of a nontrivial finite unit-circle
geometric phase from an explicit absolute phase-angle bound. This version does
not require the full `2πmθ` phase to lie in one principal interval. -/
theorem geometric_phase_norm_ratio_lower_bound_of_angle_le
    {θ A : ℝ} {m : ℕ}
    (hApos : 0 < A) (hApi : A ≤ Real.pi)
    (hangle : Real.pi * ((m : ℝ) * |θ|) ≤ A)
    (hne : Complex.exp (2 * Real.pi * θ * Complex.I) ≠ 1) :
    (m : ℝ) * (Real.sin A / A) ≤
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ /
        ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ := by
  have hθ_ne : θ ≠ 0 := by
    intro hθ
    apply hne
    simp [hθ]
  have hnum :
      2 * ((Real.sin A / A) * (Real.pi * ((m : ℝ) * |θ|))) ≤
        ‖Complex.exp (2 * Real.pi * θ * Complex.I) ^ m - 1‖ :=
    norm_exp_two_pi_mul_nat_mul_I_sub_one_lower_bound_of_angle_le
      hApos hApi hangle
  have hden :
      ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ ≤
        |2 * Real.pi * θ| :=
    norm_exp_two_pi_mul_I_sub_one_le θ
  have hden_pos :
      0 < ‖Complex.exp (2 * Real.pi * θ * Complex.I) - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hratio :=
    div_le_div₀ (norm_nonneg _) hnum hden_pos hden
  have hleft :
      (2 * ((Real.sin A / A) * (Real.pi * ((m : ℝ) * |θ|)))) /
          |2 * Real.pi * θ| =
        (m : ℝ) * (Real.sin A / A) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg Real.pi_pos.le]
    field_simp [abs_ne_zero.mpr hθ_ne, ne_of_gt hApos, ne_of_gt Real.pi_pos]
  rw [← hleft]
  exact hratio

theorem exp_pi_div_two_mul_I :
    Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I := by
  rw [show ((Real.pi : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; ring,
    exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_neg_pi_div_two_mul_I :
    Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
  rw [show -((Real.pi : ℂ) / 2 * Complex.I)
      = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- `√(1-x²)` squares back to `1 - x²` over `ℂ` for `x ∈ [-1,1]`. -/
theorem sq_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ((Real.sqrt (1 - x ^ 2) : ℂ)) ^ 2 = 1 - (x : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow,
    Real.sq_sqrt (by nlinarith [hx.1, hx.2] : (0 : ℝ) ≤ 1 - x ^ 2)]
  push_cast
  ring

/-- A phase factor solving the degree-reduction equation `e^{2iφ} q = p`,
available whenever `|p| = |q| ≠ 0` [Lin22, hermfunc.tex:1226]. -/
theorem exists_exp_sq_eq {p q : ℂ} (hq : q ≠ 0)
    (hpq : p * starRingEnd ℂ p = q * starRingEnd ℂ q) :
    ∃ φ : ℝ, Complex.exp (φ * Complex.I) ^ 2 * q = p := by
  refine ⟨(p / q).arg / 2, ?_⟩
  have hnorm : ‖p / q‖ = 1 := by
    have h1 : ‖p‖ * ‖p‖ = ‖q‖ * ‖q‖ := by
      have := congrArg norm hpq
      simpa [norm_mul, Complex.norm_conj] using this
    have h2 : ‖p‖ = ‖q‖ := by
      nlinarith [norm_nonneg p, norm_nonneg q]
    rw [norm_div, h2, div_self (norm_ne_zero_iff.mpr hq)]
  have harg : Complex.exp ((p / q).arg * Complex.I) = p / q := by
    have h := Complex.norm_mul_exp_arg_mul_I (p / q)
    rw [hnorm] at h
    simpa using h
  have hsq : Complex.exp (((p / q).arg / 2 : ℝ) * Complex.I) ^ 2
      = Complex.exp ((p / q).arg * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq, harg, div_mul_cancel₀ p hq]

theorem exp_pi_div_four_sq :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) = Complex.I := by
  rw [← Complex.exp_add, show (Real.pi : ℂ) / 4 * Complex.I
      + (Real.pi : ℂ) / 4 * Complex.I = (Real.pi : ℂ) / 2 * Complex.I by ring,
    exp_pi_div_two_mul_I]

theorem exp_pi_div_four_mul_neg :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) *
      Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- `e^{iπ/4} · i = -e^{-iπ/4}` (both equal `e^{3iπ/4}`). -/
theorem exp_pi_div_four_mul_I :
    Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) * Complex.I
      = -Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) := by
  apply mul_left_cancel₀ (Complex.exp_ne_zero ((Real.pi : ℂ) / 4 * Complex.I))
  rw [← mul_assoc, exp_pi_div_four_sq, Complex.I_mul_I, mul_neg,
    exp_pi_div_four_mul_neg]

/-- `e^{-iπ/4} · i = e^{iπ/4}`. -/
theorem exp_neg_pi_div_four_mul_I :
    Complex.exp (-((Real.pi : ℂ) / 4 * Complex.I)) * Complex.I
      = Complex.exp ((Real.pi : ℂ) / 4 * Complex.I) := by
  apply mul_left_cancel₀ (Complex.exp_ne_zero ((Real.pi : ℂ) / 4 * Complex.I))
  rw [← mul_assoc, exp_pi_div_four_mul_neg, one_mul, exp_pi_div_four_sq]

theorem ofReal_sin_sq_add_cos_sq (t : ℝ) :
    (Real.sin t : ℂ) * (Real.sin t : ℂ) + (Real.cos t : ℂ) * (Real.cos t : ℂ)
      = 1 := by
  norm_cast
  linear_combination Real.sin_sq_add_cos_sq t

/-- A unit-norm complex number is the exponential of its argument. -/
theorem exp_arg_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) :
    Complex.exp ((Complex.arg z : ℂ) * Complex.I) = z := by
  calc
    Complex.exp ((Complex.arg z : ℂ) * Complex.I)
        = (‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
          rw [hz]
          norm_num
    _ = z := Complex.norm_mul_exp_arg_mul_I z

/-- `t ↦ e^{it}` is injective on `(0, π)`. -/
theorem exp_I_injOn_Ioo :
    Set.InjOn (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Set.Ioo 0 Real.pi) := by
  intro s hs t ht hst
  simp only [] at hst
  rw [Complex.exp_eq_exp_iff_exists_int] at hst
  obtain ⟨n, hn⟩ := hst
  have h2 : ((s : ℂ)) * Complex.I
      = ((t : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
    rw [hn]; ring
  have hreal : s = t + (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2
  have hπ := Real.pi_pos
  have hn0 : n = 0 := by
    rcases lt_trichotomy n 0 with hneg | hz | hpos
    · exfalso
      have hle : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
      have hmul : (n : ℝ) * (2 * Real.pi) ≤ (-1) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
      linarith [hs.1, ht.2]
    · exact hz
    · exfalso
      have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      have hmul : (1 : ℝ) * (2 * Real.pi) ≤ (n : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
      linarith [hs.2, ht.1]
  rw [hn0] at hreal
  push_cast at hreal
  linarith

/-- `z·z* = ‖z‖²` in `ℂ`. -/
theorem mul_conj_eq_norm_sq (z : ℂ) :
    z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [map_mul, Complex.conj_ofReal, conj_exp_I]
  linear_combination ((‖z‖ : ℂ) * (‖z‖ : ℂ)) * exp_I_mul_exp_neg_I z.arg

/-- If `c / k` is a nonnegative real number, then it has a complex square-root
scale in the form needed by Laurent root-product normalizations. -/
theorem exists_scale_mul_conj_mul_eq_of_div_nonnegative_real {c k : ℂ}
    (hk : k ≠ 0) (him : (c / k).im = 0) (hre : 0 ≤ (c / k).re) :
    ∃ s : ℂ, s * starRingEnd ℂ s * k = c := by
  let r : ℝ := Real.sqrt ((c / k).re)
  have hr2 : r ^ 2 = (c / k).re := Real.sq_sqrt hre
  have hreal : (((c / k).re : ℝ) : ℂ) = c / k := by
    apply Complex.ext
    · simp
    · simpa using him.symm
  refine ⟨(r : ℂ), ?_⟩
  calc
    (r : ℂ) * starRingEnd ℂ (r : ℂ) * k =
        ((r ^ 2 : ℝ) : ℂ) * k := by
          rw [Complex.conj_ofReal]
          have hrpow : (r : ℂ) * (r : ℂ) = ((r ^ 2 : ℝ) : ℂ) := by
            norm_num [sq]
          rw [hrpow]
    _ = (((c / k).re : ℝ) : ℂ) * k := by rw [hr2]
    _ = (c / k) * k := by rw [hreal]
    _ = c := div_mul_cancel₀ c hk

/-- A unit-normalized multiple of a nonzero pair, with real product: the
phase `e^{-i·arg(pq)/2}` makes `|cp|² + |cq|² = 1` and `c²pq` real. -/
theorem exists_unit_mul {p q : ℂ} (hpq : ¬(p = 0 ∧ q = 0)) :
    ∃ c : ℂ,
      c * p * starRingEnd ℂ (c * p) + c * q * starRingEnd ℂ (c * q) = 1 ∧
      (c * p * (c * q)).im = 0 := by
  have hpos : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rcases not_and_or.mp hpq with hp | hq
    · have h1 : 0 < ‖p‖ := norm_pos_iff.mpr hp
      nlinarith [sq_nonneg ‖q‖]
    · have h1 : 0 < ‖q‖ := norm_pos_iff.mpr hq
      nlinarith [sq_nonneg ‖p‖]
  set r : ℝ := Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := Real.sq_sqrt hpos.le
  set μ : ℝ := -(p * q).arg / 2 with hμdef
  set c : ℂ := ((r⁻¹ : ℝ) : ℂ) * Complex.exp ((μ : ℂ) * Complex.I)
    with hcdef
  clear_value c
  have hcc : c * starRingEnd ℂ c = ((r⁻¹ ^ 2 : ℝ) : ℂ) := by
    rw [hcdef, map_mul, Complex.conj_ofReal, conj_exp_I]
    push_cast
    linear_combination ((r : ℂ))⁻¹ * ((r : ℂ))⁻¹ * exp_I_mul_exp_neg_I μ
  refine ⟨c, ?_, ?_⟩
  · have hsum : p * starRingEnd ℂ p + q * starRingEnd ℂ q
        = ((r ^ 2 : ℝ) : ℂ) := by
      rw [mul_conj_eq_norm_sq, mul_conj_eq_norm_sq, hr2]
      push_cast
      ring
    calc c * p * starRingEnd ℂ (c * p) + c * q * starRingEnd ℂ (c * q)
        = (c * starRingEnd ℂ c)
            * (p * starRingEnd ℂ p + q * starRingEnd ℂ q) := by
          rw [map_mul, map_mul]; ring
      _ = ((r⁻¹ ^ 2 : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ) := by rw [hcc, hsum]
      _ = 1 := by
          norm_cast
          rw [inv_pow]
          exact inv_mul_cancel₀ (pow_ne_zero 2 hrpos.ne')
  · have hexp : Complex.exp ((μ : ℂ) * Complex.I)
        * Complex.exp ((μ : ℂ) * Complex.I)
        * Complex.exp (((p * q).arg : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      rw [show (μ : ℂ) * Complex.I + (μ : ℂ) * Complex.I
          + ((p * q).arg : ℂ) * Complex.I
          = ((μ + μ + (p * q).arg : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [show (μ + μ + (p * q).arg : ℝ) = 0 by rw [hμdef]; ring]
      simp
    have hprod : c * p * (c * q) = ((r⁻¹ ^ 2 * ‖p * q‖ : ℝ) : ℂ) := by
      calc c * p * (c * q) = c * c * (p * q) := by ring
        _ = ((r⁻¹ : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ) * ((‖p * q‖ : ℝ) : ℂ)
            * (Complex.exp ((μ : ℂ) * Complex.I)
              * Complex.exp ((μ : ℂ) * Complex.I)
              * Complex.exp (((p * q).arg : ℂ) * Complex.I)) := by
            rw [hcdef]
            conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (p * q)]
            ring
        _ = ((r⁻¹ ^ 2 * ‖p * q‖ : ℝ) : ℂ) := by
            rw [hexp, mul_one]
            push_cast
            ring
    rw [hprod]
    exact Complex.ofReal_im _

/-- A unit-normalized positive multiple of a nonzero real pair. -/
theorem exists_real_unit {p q : ℝ} (hpq : ¬(p = 0 ∧ q = 0)) :
    ∃ v w : ℝ, v ^ 2 + w ^ 2 = 1 ∧ ∃ c : ℝ, v = c * p ∧ w = c * q := by
  have hpos : 0 < p ^ 2 + q ^ 2 := by
    rcases not_and_or.mp hpq with hp | hq
    · rcases lt_or_gt_of_ne hp with h | h <;> nlinarith [sq_nonneg q]
    · rcases lt_or_gt_of_ne hq with h | h <;> nlinarith [sq_nonneg p]
  set r : ℝ := Real.sqrt (p ^ 2 + q ^ 2) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
  have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpos.le
  refine ⟨r⁻¹ * p, r⁻¹ * q, ?_, r⁻¹, rfl, rfl⟩
  have h1 : (r⁻¹ * p) ^ 2 + (r⁻¹ * q) ^ 2 = r⁻¹ ^ 2 * (p ^ 2 + q ^ 2) := by
    ring
  rw [h1, ← hr2, inv_pow]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hrpos.ne')

/-- Any point of the real unit circle is `(cos(θ/2), sin(θ/2))` for some
angle `θ`. -/
theorem exists_cos_sin {v w : ℝ} (hvw : v ^ 2 + w ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos (θ / 2) = v ∧ Real.sin (θ / 2) = w := by
  set ζ : ℂ := (v : ℂ) + (w : ℂ) * Complex.I with hζdef
  have hC : (v : ℂ) ^ 2 + (w : ℂ) ^ 2 = 1 := by exact_mod_cast hvw
  have hζconj : ζ * starRingEnd ℂ ζ = 1 := by
    rw [hζdef]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    linear_combination (-(w : ℂ) ^ 2) * Complex.I_sq + hC
  have hn1 : ‖ζ‖ = 1 := by
    have h1 := mul_conj_eq_norm_sq ζ
    rw [hζconj] at h1
    have h2 : ‖ζ‖ ^ 2 = 1 := by exact_mod_cast h1.symm
    have h4 : (‖ζ‖ - 1) * (‖ζ‖ + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · exfalso; linarith [norm_nonneg ζ]
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn1
    norm_num at hn1
  refine ⟨2 * ζ.arg, ?_, ?_⟩
  · rw [show (2 * ζ.arg) / 2 = ζ.arg by ring, Complex.cos_arg hζ0, hn1,
      div_one, hζdef]
    simp
  · rw [show (2 * ζ.arg) / 2 = ζ.arg by ring, Complex.sin_arg, hn1,
      div_one, hζdef]
    simp

end QuantumAlg
