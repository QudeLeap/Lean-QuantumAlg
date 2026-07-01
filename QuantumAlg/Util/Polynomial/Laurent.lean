/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Polynomial.Basic

/-!
# Laurent polynomial evaluation helpers

Quantum-free helpers for the Fourier/Laurent representation used by QSP.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

/-- `e^{-iLx/2}·F(e^{ix})`: the value at `z = e^{ix/2}` of the Laurent
polynomial `z^{-L}·F(z²)` encoded by `F : ℂ[X]`. -/
def lEval (L : ℕ) (F : ℂ[X]) (x : ℝ) : ℂ :=
  Complex.exp (-((L * x / 2 : ℝ) * Complex.I)) *
    F.eval (Complex.exp ((x : ℂ) * Complex.I))

/-- Convert the centered Laurent evaluation back to ordinary polynomial
evaluation on the unit circle. -/
theorem eval_exp_eq_exp_mul_lEval (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    F.eval (Complex.exp ((x : ℂ) * Complex.I)) =
      Complex.exp (((L * x / 2 : ℝ) : ℂ) * Complex.I) * lEval L F x := by
  rw [lEval]
  calc
    F.eval (Complex.exp ((x : ℂ) * Complex.I)) =
        1 * F.eval (Complex.exp ((x : ℂ) * Complex.I)) := by simp
    _ =
        (Complex.exp (((L * x / 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(((L * x / 2 : ℝ) : ℂ) * Complex.I))) *
          F.eval (Complex.exp ((x : ℂ) * Complex.I)) := by
          rw [exp_I_mul_exp_neg_I]
    _ =
        Complex.exp (((L * x / 2 : ℝ) : ℂ) * Complex.I) *
          (Complex.exp (-(((L * x / 2 : ℝ) : ℂ) * Complex.I)) *
            F.eval (Complex.exp ((x : ℂ) * Complex.I))) := by ring

/-- Ordinary polynomial zeros on the unit circle are exactly zeros of the
centered Laurent evaluation. -/
theorem eval_exp_eq_zero_iff_lEval_eq_zero (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    F.eval (Complex.exp ((x : ℂ) * Complex.I)) = 0 ↔ lEval L F x = 0 := by
  rw [eval_exp_eq_exp_mul_lEval]
  constructor
  · intro hzero
    rw [mul_eq_zero] at hzero
    rcases hzero with hexp | hl
    · exact False.elim ((Complex.exp_ne_zero _) hexp)
    · exact hl
  · intro hl
    rw [hl, mul_zero]

/-- A complex number with squared norm `1` has a real unit-circle phase. -/
theorem exists_phase_of_normSq_eq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    ∃ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) = z := by
  have hsq : ‖z‖ ^ 2 = (1 : ℝ) ^ 2 := by
    simpa [Complex.normSq_eq_norm_sq] using hz
  have habs : |‖z‖| = |(1 : ℝ)| :=
    (sq_eq_sq_iff_abs_eq_abs ‖z‖ (1 : ℝ)).mp hsq
  have hnorm : ‖z‖ = 1 := by
    simpa [abs_of_nonneg (norm_nonneg z)] using habs
  exact ⟨Complex.arg z, exp_arg_of_norm_eq_one z hnorm⟩

/-- Root form of `eval_exp_eq_zero_iff_lEval_eq_zero` for an arbitrary
unit-circle point. -/
theorem exists_phase_lEval_eq_zero_of_eval_eq_zero {L : ℕ} {F : ℂ[X]} {z : ℂ}
    (hunit : Complex.normSq z = 1) (hroot : F.eval z = 0) :
    ∃ x : ℝ, Complex.exp ((x : ℂ) * Complex.I) = z ∧ lEval L F x = 0 := by
  rcases exists_phase_of_normSq_eq_one hunit with ⟨x, rfl⟩
  exact ⟨x, rfl, (eval_exp_eq_zero_iff_lEval_eq_zero L F x).mp hroot⟩

theorem lEval_C_mul (L : ℕ) (c : ℂ) (F : ℂ[X]) (x : ℝ) :
    lEval L (C c * F) x = c * lEval L F x := by
  rw [lEval, lEval, Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem lEval_add (L : ℕ) (F G : ℂ[X]) (x : ℝ) :
    lEval L (F + G) x = lEval L F x + lEval L G x := by
  rw [lEval, lEval, lEval, Polynomial.eval_add]
  ring

theorem lEval_sub (L : ℕ) (F G : ℂ[X]) (x : ℝ) :
    lEval L (F - G) x = lEval L F x - lEval L G x := by
  rw [lEval, lEval, lEval, Polynomial.eval_sub]
  ring

/-- Raising the parity budget multiplies the encoded value by `e^{-ix/2}`. -/
theorem lEval_succ (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    lEval (L + 1) F x
      = Complex.exp (-(((x / 2 : ℝ) : ℂ) * Complex.I)) * lEval L F x := by
  rw [lEval, lEval, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Raising the budget while multiplying by `X` multiplies by `e^{ix/2}`. -/
theorem lEval_succ_X_mul (L : ℕ) (F : ℂ[X]) (x : ℝ) :
    lEval (L + 1) (X * F) x
      = Complex.exp (((x / 2 : ℝ) : ℂ) * Complex.I) * lEval L F x := by
  rw [lEval, lEval, Polynomial.eval_mul, Polynomial.eval_X, ← mul_assoc,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The encoded value of a constant at budget `0`. -/
theorem lEval_zero_C (c : ℂ) (x : ℝ) : lEval 0 (C c) x = c := by
  rw [lEval, Polynomial.eval_C]
  norm_num

/-- The centered monomial evaluates to `1` under the doubled Laurent budget:
`e^{-i(2L)x/2}(e^{ix})^L = 1`. -/
theorem lEval_two_mul_X_pow (L : ℕ) (x : ℝ) :
    lEval (2 * L) (X ^ L : ℂ[X]) x = 1 := by
  rw [lEval, Polynomial.eval_pow, Polynomial.eval_X, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  have harg :
      -(↑(↑(2 * L) * x / 2) * Complex.I) +
          (↑L : ℂ) * ((x : ℂ) * Complex.I) = 0 := by
    push_cast
    ring
  rw [harg, Complex.exp_zero]

/-- Conjugating the encoded value reflects the conjugated coefficients. -/
theorem conj_lEval {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) (x : ℝ) :
    starRingEnd ℂ (lEval L F x) = lEval L ((conjP F).reflect L) x := by
  have hw : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hFc : (conjP F).natDegree ≤ L :=
    le_trans (Polynomial.natDegree_map_le) hF
  have h1 : (conjP F).eval (Complex.exp (-((x : ℂ) * Complex.I)))
      = starRingEnd ℂ (F.eval (Complex.exp ((x : ℂ) * Complex.I))) := by
    rw [← conj_exp_I, conjP, Polynomial.eval_map, Polynomial.eval₂_hom]
  rw [lEval, map_mul, conj_exp_neg_I, ← h1, lEval, eval_reflect hFc hw,
    ← Complex.exp_neg, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The conjugate-pair product under `lEval`, encoded as one Laurent
polynomial at the doubled degree budget.  This is the quantum-free algebraic
identity behind the normalization equations for trigonometric QSP and QPP. -/
theorem lEval_mul_conj {L : ℕ} {F : ℂ[X]} (hF : F.natDegree ≤ L) (x : ℝ) :
    lEval L F x * starRingEnd ℂ (lEval L F x)
      = lEval (2 * L) (F * (conjP F).reflect L) x := by
  rw [conj_lEval hF x]
  unfold lEval
  rw [Polynomial.eval_mul]
  calc
    Complex.exp (-(↑(↑L * x / 2) * Complex.I)) *
        F.eval (Complex.exp (↑x * Complex.I)) *
        (Complex.exp (-(↑(↑L * x / 2) * Complex.I)) *
          ((conjP F).reflect L).eval (Complex.exp (↑x * Complex.I))) =
      (Complex.exp (-(↑(↑L * x / 2) * Complex.I)) *
          Complex.exp (-(↑(↑L * x / 2) * Complex.I))) *
        (F.eval (Complex.exp (↑x * Complex.I)) *
          ((conjP F).reflect L).eval (Complex.exp (↑x * Complex.I))) := by
        ring
    _ =
      Complex.exp (-(↑(↑(2 * L) * x / 2) * Complex.I)) *
        (F.eval (Complex.exp (↑x * Complex.I)) *
          ((conjP F).reflect L).eval (Complex.exp (↑x * Complex.I))) := by
        congr 1
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring

end

end QuantumAlg
