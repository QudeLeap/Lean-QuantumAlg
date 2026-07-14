/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Banach-algebra exponentials of idempotents and involutions (quantum-free)

Two closed forms for `NormedSpace.exp` of a scalar multiple of a special element in a complex
Banach algebra `A`.

## Main results

- `QuantumAlg.exp_smul_isIdempotentElem` — for an idempotent `P` (`P * P = P`),
  `exp (c • P) = 1 + (Complex.exp c - 1) • P`.
- `QuantumAlg.exp_smul_of_mul_self_eq_one` — for an involution `H` (`H * H = 1`),
  `exp (z • H) = Complex.cosh z • 1 + Complex.sinh z • H`.

These are pure Banach-algebra analysis lemmas with no quantum content; they feed the
parameter-shift / generator machinery downstream where generators square to `1` (involutions)
or are spectral projectors (idempotents).

In Mathlib `v4.31.0` the operator exponential `NormedSpace.exp : A → A` carries no explicit field
argument (the scalar field only appears on `NormedSpace.exp_eq_tsum`); we therefore write
`NormedSpace.exp (c • P)` rather than the older `NormedSpace.exp ℂ (c • P)`.

Pinned Mathlib API: `NormedSpace.exp_eq_tsum`, `NormedSpace.expSeries_summable'`,
`NormedSpace.expSeries_radius_eq_top`, `NormedSpace.exp_add_of_commute_of_mem_ball`,
`Complex.exp_eq_exp_ℂ`, `Summable.tsum_eq_zero_add`, `Summable.tsum_smul_const`,
`summable_nat_add_iff`, `Complex.cosh`, `Complex.sinh`.
-/

@[expose] public section

namespace QuantumAlg

open NormedSpace

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- For an idempotent `P` (`P * P = P`), every positive power collapses: `P ^ (n + 1) = P`. -/
private theorem idem_pow_succ {P : A} (hP : IsIdempotentElem P) (n : ℕ) : P ^ (n + 1) = P := by
  induction n with
  | zero => exact pow_one P
  | succ k ih => rw [pow_succ, ih, hP.eq]

/-- `exp` is multiplicative on commuting elements.

This is `NormedSpace.exp_add_of_commute` specialised to the field `ℂ`. The library version lives in
the `ℚ`-algebra section and needs `[NormedAlgebra ℚ A]`, which is not available from our
`[NormedAlgebra ℂ A]` hypotheses alone; we instead invoke the field-generic
`NormedSpace.exp_add_of_commute_of_mem_ball` over `ℂ`, where the disk of convergence is all of `A`
(`NormedSpace.expSeries_radius_eq_top`). -/
theorem exp_add_of_commute_ℂ {x y : A} (h : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y := by
  have hradius : (NormedSpace.expSeries ℂ A).radius = ⊤ := NormedSpace.expSeries_radius_eq_top ℂ A
  exact NormedSpace.exp_add_of_commute_of_mem_ball h
    (hradius.symm ▸ edist_lt_top _ _) (hradius.symm ▸ edist_lt_top _ _)

/-- **Exponential of a scalar multiple of an idempotent.**
In a complex Banach algebra, if `P * P = P` then
`exp (c • P) = 1 + (Complex.exp c - 1) • P`. -/
theorem exp_smul_isIdempotentElem (c : ℂ) {P : A} (hP : IsIdempotentElem P) :
    NormedSpace.exp (c • P) = 1 + (Complex.exp c - 1) • P := by
  -- Expand the operator exponential as a tsum, with the field `ℂ`.
  rw [NormedSpace.exp_eq_tsum ℂ]
  -- Each term `(n!⁻¹) • (c • P) ^ n = (n!⁻¹ * c ^ n) • P ^ n`.
  have hterm : ∀ n : ℕ,
      ((n.factorial : ℂ)⁻¹ • (c • P) ^ n) = ((n.factorial : ℂ)⁻¹ * c ^ n) • P ^ n :=
    fun n => by rw [smul_pow, smul_smul]
  simp only [hterm]
  -- Summability of the rewritten series.
  have hsummable : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ * c ^ n) • P ^ n) := by
    simpa only [hterm] using (NormedSpace.expSeries_summable' (𝕂 := ℂ) (c • P))
  -- Split off the `n = 0` term: `f 0 = 1`, tail `f (n + 1) = ((n+1)!⁻¹ * c^(n+1)) • P`.
  rw [hsummable.tsum_eq_zero_add]
  -- The `n = 0` term is `1`; the tail collapses since `P ^ (n + 1) = P`.
  have htail : ∀ n : ℕ, ((((n + 1).factorial : ℂ)⁻¹ * c ^ (n + 1)) • P ^ (n + 1))
      = ((((n + 1).factorial : ℂ)⁻¹ * c ^ (n + 1)) • P) := fun n => by rw [idem_pow_succ hP]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, mul_one, one_smul, htail]
  -- Pull `P` out of the tail tsum.
  have hscalar_summable : Summable (fun n : ℕ => ((n + 1).factorial : ℂ)⁻¹ * c ^ (n + 1)) := by
    have hexp : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ * c ^ n)) := by
      simpa using (NormedSpace.expSeries_summable' (𝕂 := ℂ) c)
    exact (summable_nat_add_iff 1).2 hexp
  rw [hscalar_summable.tsum_smul_const]
  -- The scalar tail equals `Complex.exp c - 1`.
  have htsum : (∑' n : ℕ, ((n + 1).factorial : ℂ)⁻¹ * c ^ (n + 1)) = Complex.exp c - 1 := by
    have hsc_summable : Summable (fun n : ℕ => ((n.factorial : ℂ)⁻¹ * c ^ n)) := by
      have hterm' : ∀ n : ℕ, ((n.factorial : ℂ)⁻¹ • c ^ n) = ((n.factorial : ℂ)⁻¹ * c ^ n) :=
        fun n => by rw [smul_eq_mul]
      simpa [hterm'] using (NormedSpace.expSeries_summable' (𝕂 := ℂ) c)
    have hexpand : Complex.exp c = ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * c ^ n) := by
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ]
      exact tsum_congr fun n => by rw [smul_eq_mul]
    rw [hexpand, hsc_summable.tsum_eq_zero_add]
    simp
  rw [htsum]

/-- **Exponential of a scalar multiple of an involution.**
In a complex Banach algebra, if `H * H = 1` then
`exp (z • H) = Complex.cosh z • 1 + Complex.sinh z • H`. -/
theorem exp_smul_of_mul_self_eq_one (z : ℂ) {H : A} (hH : H * H = 1) :
    NormedSpace.exp (z • H) = Complex.cosh z • (1 : A) + Complex.sinh z • H := by
  -- The two complementary spectral projectors of the involution `H`.
  set P : A := (2⁻¹ : ℂ) • (1 + H) with hPdef
  set Q : A := (2⁻¹ : ℂ) • (1 - H) with hQdef
  -- `P` and `Q` are idempotents: `(1 ± H)(1 ± H) = 2(1 ± H)` since `H * H = 1`.
  have hPidem : IsIdempotentElem P := by
    change P * P = P
    rw [hPdef, smul_mul_smul_comm]
    have hinner : (1 + H) * (1 + H) = (2 : ℂ) • (1 + H) := by
      rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, hH]
      match_scalars <;> ring
    rw [hinner, smul_smul]; norm_num
  have hQidem : IsIdempotentElem Q := by
    change Q * Q = Q
    rw [hQdef, smul_mul_smul_comm]
    have hinner : (1 - H) * (1 - H) = (2 : ℂ) • (1 - H) := by
      rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, hH]
      match_scalars <;> ring
    rw [hinner, smul_smul]; norm_num
  -- `z • H = z • P + (-z) • Q`, because `P - Q = H`.
  have hsplit : z • H = z • P + (-z) • Q := by
    rw [hPdef, hQdef]; match_scalars <;> ring
  -- `P` and `Q` annihilate each other: `(1 + H)(1 - H) = 1 - H*H = 0` and symmetrically.
  have hPQ : P * Q = 0 := by
    rw [hPdef, hQdef, smul_mul_smul_comm]
    have hinner : (1 + H) * (1 - H) = 0 := by
      rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, hH]; abel
    rw [hinner, smul_zero]
  have hQP : Q * P = 0 := by
    rw [hPdef, hQdef, smul_mul_smul_comm]
    have hinner : (1 - H) * (1 + H) = 0 := by
      rw [mul_add, sub_mul, sub_mul, one_mul, mul_one, one_mul, hH]; abel
    rw [hinner, smul_zero]
  -- `z • P` and `(-z) • Q` commute (both products vanish, so `P` and `Q` commute).
  have hbase : Commute P Q := show P * Q = Q * P by rw [hPQ, hQP]
  have hcomm : Commute (z • P) ((-z) • Q) := (hbase.smul_left z).smul_right (-z)
  -- Multiplicativity of `exp` on the commuting summands, then Theorem 1 on each factor.
  rw [hsplit, exp_add_of_commute_ℂ hcomm,
    exp_smul_isIdempotentElem z hPidem, exp_smul_isIdempotentElem (-z) hQidem]
  -- Expand the product `(1 + a • P) * (1 + b • Q)` using `P * Q = 0`.
  have hcross : ((Complex.exp z - 1) • P) * ((Complex.exp (-z) - 1) • Q) = 0 := by
    rw [smul_mul_smul_comm, hPQ, smul_zero]
  rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, hcross, add_zero]
  -- Substitute `P` and `Q` back and collect into `cosh`/`sinh`.
  rw [Complex.cosh, Complex.sinh, hPdef, hQdef]
  -- Reduce to scalar identities for the coefficients of `1` and `H`.
  match_scalars
  · ring
  · ring

end BanachAlgebra

end QuantumAlg
