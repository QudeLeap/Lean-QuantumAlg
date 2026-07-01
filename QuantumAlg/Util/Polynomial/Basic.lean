/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Interval.Set.Infinite
public import QuantumAlg.Util.Complex

/-!
# Polynomial helper lemmas (quantum-free)

Generic `ℂ[X]` lemmas used by the QSP development, factored out so they carry
no dependency on the quantum framework:

- `conjP` — coefficient-conjugate of a polynomial (the `P*` of the QSP
  literature) and its ring/eval lemmas;
- `HasParity` — the predicate "all nonzero coefficients sit in degrees of a
  fixed parity" and its closure lemmas;
- total coefficient formulas (`coeff_X_mul'`, `coeff_X_sq_mul`) and bounded
  product-coefficient lemmas;
- `Polynomial.reflect` coefficient/evaluation lemmas;
- `eq_of_circle_eval_eq` — two polynomials agreeing on the unit circle are equal.

These are upstream candidates for Mathlib; nothing here mentions `Gate`/`PureState`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

/-! ### Real-to-complex coefficient lift -/

/-- Lift a real-coefficient polynomial to complex coefficients. -/
noncomputable def realPolynomialToComplex (P : ℝ[X]) : ℂ[X] :=
  P.map (algebraMap ℝ ℂ)

@[simp]
theorem realPolynomialToComplex_zero : realPolynomialToComplex 0 = 0 :=
  Polynomial.map_zero _

@[simp]
theorem realPolynomialToComplex_one : realPolynomialToComplex 1 = 1 :=
  Polynomial.map_one _

@[simp]
theorem realPolynomialToComplex_X : realPolynomialToComplex X = X :=
  Polynomial.map_X _

@[simp]
theorem realPolynomialToComplex_C (c : ℝ) :
    realPolynomialToComplex (C c) = C (c : ℂ) :=
  Polynomial.map_C _

@[simp]
theorem realPolynomialToComplex_neg (P : ℝ[X]) :
    realPolynomialToComplex (-P) = -realPolynomialToComplex P :=
  Polynomial.map_neg _

@[simp]
theorem realPolynomialToComplex_add (P Q : ℝ[X]) :
    realPolynomialToComplex (P + Q) =
      realPolynomialToComplex P + realPolynomialToComplex Q :=
  Polynomial.map_add _

@[simp]
theorem realPolynomialToComplex_sub (P Q : ℝ[X]) :
    realPolynomialToComplex (P - Q) =
      realPolynomialToComplex P - realPolynomialToComplex Q :=
  Polynomial.map_sub _

@[simp]
theorem realPolynomialToComplex_mul (P Q : ℝ[X]) :
    realPolynomialToComplex (P * Q) =
      realPolynomialToComplex P * realPolynomialToComplex Q :=
  Polynomial.map_mul _

@[simp]
theorem realPolynomialToComplex_pow (P : ℝ[X]) (n : ℕ) :
    realPolynomialToComplex (P ^ n) = realPolynomialToComplex P ^ n :=
  Polynomial.map_pow _ _

theorem realPolynomialToComplex_eval_ofReal (P : ℝ[X]) (x : ℝ) :
    (realPolynomialToComplex P).eval (x : ℂ) =
      ((Polynomial.eval x P : ℝ) : ℂ) := by
  simpa [realPolynomialToComplex] using
    (Polynomial.eval_map_apply (f := (algebraMap ℝ ℂ)) (p := P) x)

/-- The real-to-complex coefficient embedding is injective on polynomials. -/
theorem realPolynomialToComplex_injective :
    Function.Injective realPolynomialToComplex := by
  intro P Q h
  ext n
  have hcoeff := congrArg (fun R : ℂ[X] => R.coeff n) h
  have hcoeff' : (P.coeff n : ℂ) = (Q.coeff n : ℂ) := by
    simpa [realPolynomialToComplex] using hcoeff
  exact Complex.ofReal_injective hcoeff'

theorem realPolynomialToComplex_coeff_eq_zero_of_natDegree_lt {P : ℝ[X]} {m : ℕ}
    (h : P.natDegree < m) : (realPolynomialToComplex P).coeff m = 0 := by
  rw [realPolynomialToComplex, Polynomial.coeff_map]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt h]

/-- Real part of a complex-coefficient polynomial, taken coefficientwise. -/
noncomputable def complexPolynomialRealPart (P : ℂ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.mapRange Complex.re (by simp))

/-- Imaginary part of a complex-coefficient polynomial, taken coefficientwise. -/
noncomputable def complexPolynomialImagPart (P : ℂ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.mapRange Complex.im (by simp))

@[simp]
theorem complexPolynomialRealPart_coeff (P : ℂ[X]) (n : ℕ) :
    (complexPolynomialRealPart P).coeff n = (P.coeff n).re := by
  rw [complexPolynomialRealPart, Polynomial.coeff_ofFinsupp]
  simp [Polynomial.toFinsupp_apply]

@[simp]
theorem complexPolynomialImagPart_coeff (P : ℂ[X]) (n : ℕ) :
    (complexPolynomialImagPart P).coeff n = (P.coeff n).im := by
  rw [complexPolynomialImagPart, Polynomial.coeff_ofFinsupp]
  simp [Polynomial.toFinsupp_apply]

/-- A complex polynomial is reconstructed from its coefficientwise real and
imaginary parts. -/
theorem complexPolynomial_recompose (P : ℂ[X]) :
    realPolynomialToComplex (complexPolynomialRealPart P) +
        Polynomial.C Complex.I * realPolynomialToComplex (complexPolynomialImagPart P) = P := by
  ext n
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
  simp [realPolynomialToComplex, Polynomial.coeff_map]
  simpa [mul_comm] using Complex.re_add_im (P.coeff n)

/-- Taking the coefficientwise real part does not increase degree. -/
theorem complexPolynomialRealPart_natDegree_le (P : ℂ[X]) :
    (complexPolynomialRealPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialRealPart_coeff]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Taking the coefficientwise imaginary part does not increase degree. -/
theorem complexPolynomialImagPart_natDegree_le (P : ℂ[X]) :
    (complexPolynomialImagPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialImagPart_coeff]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- Evaluation of the coefficientwise real part at a real point. -/
theorem complexPolynomialRealPart_eval_ofReal (P : ℂ[X]) (x : ℝ) :
    (complexPolynomialRealPart P).eval x = (P.eval (x : ℂ)).re := by
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (complexPolynomialRealPart_natDegree_le P) : _),
    Polynomial.eval_eq_sum_range]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp [complexPolynomialRealPart_coeff, ← Complex.ofReal_pow]

/-- Evaluation of the coefficientwise imaginary part at a real point. -/
theorem complexPolynomialImagPart_eval_ofReal (P : ℂ[X]) (x : ℝ) :
    (complexPolynomialImagPart P).eval x = (P.eval (x : ℂ)).im := by
  rw [Polynomial.eval_eq_sum_range'
    (Nat.lt_succ_of_le (complexPolynomialImagPart_natDegree_le P) : _),
    Polynomial.eval_eq_sum_range]
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  simp [complexPolynomialImagPart_coeff, ← Complex.ofReal_pow]

/-- Even coefficient part of a real polynomial. -/
noncomputable def realPolynomialEvenPart (P : ℝ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.filter fun n => n % 2 = 0)

/-- Odd coefficient part of a real polynomial. -/
noncomputable def realPolynomialOddPart (P : ℝ[X]) : ℝ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.filter fun n => n % 2 = 1)

@[simp]
theorem realPolynomialEvenPart_coeff (P : ℝ[X]) (n : ℕ) :
    (realPolynomialEvenPart P).coeff n = if n % 2 = 0 then P.coeff n else 0 := by
  rw [realPolynomialEvenPart, Polynomial.coeff_ofFinsupp]
  by_cases h : n % 2 = 0 <;> simp [h, Polynomial.toFinsupp_apply]

@[simp]
theorem realPolynomialOddPart_coeff (P : ℝ[X]) (n : ℕ) :
    (realPolynomialOddPart P).coeff n = if n % 2 = 1 then P.coeff n else 0 := by
  rw [realPolynomialOddPart, Polynomial.coeff_ofFinsupp]
  by_cases h : n % 2 = 1 <;> simp [h, Polynomial.toFinsupp_apply]

/-- Even coefficient part of a complex polynomial.  It is written through the
coefficientwise real/imaginary parts so the API follows the complex-polynomial
split used after `thm:arbParity` in Gilyen--Su--Low--Wiebe. -/
noncomputable def complexPolynomialEvenPart (P : ℂ[X]) : ℂ[X] :=
  realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialRealPart P)) +
    Polynomial.C Complex.I *
      realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialImagPart P))

/-- Odd coefficient part of a complex polynomial. -/
noncomputable def complexPolynomialOddPart (P : ℂ[X]) : ℂ[X] :=
  realPolynomialToComplex (realPolynomialOddPart (complexPolynomialRealPart P)) +
    Polynomial.C Complex.I *
      realPolynomialToComplex (realPolynomialOddPart (complexPolynomialImagPart P))

@[simp]
theorem complexPolynomialEvenPart_coeff (P : ℂ[X]) (n : ℕ) :
    (complexPolynomialEvenPart P).coeff n = if n % 2 = 0 then P.coeff n else 0 := by
  rw [complexPolynomialEvenPart, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  by_cases h : n % 2 = 0
  · simp [h, realPolynomialToComplex, Polynomial.coeff_map]
    simpa [mul_comm] using Complex.re_add_im (P.coeff n)
  · have hodd : n % 2 = 1 := by omega
    simp [hodd, realPolynomialToComplex, Polynomial.coeff_map]

@[simp]
theorem complexPolynomialOddPart_coeff (P : ℂ[X]) (n : ℕ) :
    (complexPolynomialOddPart P).coeff n = if n % 2 = 1 then P.coeff n else 0 := by
  rw [complexPolynomialOddPart, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  by_cases h : n % 2 = 1
  · simp [h, realPolynomialToComplex, Polynomial.coeff_map]
    simpa [mul_comm] using Complex.re_add_im (P.coeff n)
  · have heven : n % 2 = 0 := by omega
    simp [heven, realPolynomialToComplex, Polynomial.coeff_map]

/-- Real polynomials split into their even and odd coefficient parts. -/
theorem realPolynomial_evenPart_add_oddPart (P : ℝ[X]) :
    realPolynomialEvenPart P + realPolynomialOddPart P = P := by
  ext n
  by_cases heven : n % 2 = 0
  · have hodd : n % 2 ≠ 1 := by omega
    simp [heven]
  · have hodd : n % 2 = 1 := by omega
    simp [hodd]

/-- Complex polynomials split into their even and odd coefficient parts. -/
theorem complexPolynomial_evenPart_add_oddPart (P : ℂ[X]) :
    complexPolynomialEvenPart P + complexPolynomialOddPart P = P := by
  ext n
  rw [Polynomial.coeff_add]
  by_cases heven : n % 2 = 0
  · simp [heven]
  · have hodd : n % 2 = 1 := by omega
    simp [hodd]

/-- Taking the even coefficient part does not increase degree. -/
theorem realPolynomialEvenPart_natDegree_le (P : ℝ[X]) :
    (realPolynomialEvenPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [realPolynomialEvenPart_coeff]
  by_cases h : n % 2 = 0
  · simp [h, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  · simp [h]

/-- Taking the odd coefficient part does not increase degree. -/
theorem realPolynomialOddPart_natDegree_le (P : ℝ[X]) :
    (realPolynomialOddPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [realPolynomialOddPart_coeff]
  by_cases h : n % 2 = 1
  · simp [h, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  · simp [h]

/-- Taking the even coefficient part of a complex polynomial does not increase
degree. -/
theorem complexPolynomialEvenPart_natDegree_le (P : ℂ[X]) :
    (complexPolynomialEvenPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialEvenPart_coeff]
  by_cases h : n % 2 = 0
  · simp [h, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  · simp [h]

/-- Taking the odd coefficient part of a complex polynomial does not increase
degree. -/
theorem complexPolynomialOddPart_natDegree_le (P : ℂ[X]) :
    (complexPolynomialOddPart P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialOddPart_coeff]
  by_cases h : n % 2 = 1
  · simp [h, Polynomial.coeff_eq_zero_of_natDegree_lt hn]
  · simp [h]

/-- If a complex polynomial has degree at most an odd `L`, then its even
coefficient part has degree at most `L - 1`. -/
theorem complexPolynomialEvenPart_natDegree_le_pred_of_odd_bound (P : ℂ[X])
    {L : ℕ} (hdegree : P.natDegree ≤ L) (hL : L % 2 = 1) :
    (complexPolynomialEvenPart P).natDegree ≤ L - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialEvenPart_coeff]
  by_cases hpar : n % 2 = 0
  · have hLn : L ≤ n := by omega
    rcases lt_or_eq_of_le hLn with hlt | rfl
    · simp [hpar, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlt)]
    · have : ¬ L % 2 = 0 := by omega
      exact False.elim (this hpar)
  · simp [hpar]

/-- If a complex polynomial has degree at most an even `L`, then its odd
coefficient part has degree at most `L - 1`. -/
theorem complexPolynomialOddPart_natDegree_le_pred_of_even_bound (P : ℂ[X])
    {L : ℕ} (hdegree : P.natDegree ≤ L) (hL : L % 2 = 0) :
    (complexPolynomialOddPart P).natDegree ≤ L - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [complexPolynomialOddPart_coeff]
  by_cases hpar : n % 2 = 1
  · have hLn : L ≤ n := by omega
    rcases lt_or_eq_of_le hLn with hlt | rfl
    · simp [hpar, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlt)]
    · have : ¬ L % 2 = 1 := by omega
      exact False.elim (this hpar)
  · simp [hpar]

/-- A degree-zero complex polynomial has no odd coefficient part. -/
theorem complexPolynomialOddPart_eq_zero_of_natDegree_eq_zero (P : ℂ[X])
    (hdeg : P.natDegree = 0) :
    complexPolynomialOddPart P = 0 := by
  ext n
  rw [complexPolynomialOddPart_coeff, Polynomial.coeff_zero]
  by_cases hn : n % 2 = 1
  · have hnpos : 0 < n := by omega
    have hcoeff : P.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hn, hcoeff]
  · simp [hn]

/-- A degree-zero real polynomial has no odd coefficient part. -/
theorem realPolynomialOddPart_eq_zero_of_natDegree_eq_zero (P : ℝ[X])
    (hdeg : P.natDegree = 0) :
    realPolynomialOddPart P = 0 := by
  ext n
  rw [realPolynomialOddPart_coeff, Polynomial.coeff_zero]
  by_cases hn : n % 2 = 1
  · have hnpos : 0 < n := by omega
    have hcoeff : P.coeff n = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hn, hcoeff]
  · simp [hn]

/-- If a polynomial has degree at most an odd `L`, then its even coefficient
part has degree at most `L - 1`. -/
theorem realPolynomialEvenPart_natDegree_le_pred_of_odd_bound (P : ℝ[X]) {L : ℕ}
    (hdegree : P.natDegree ≤ L) (hL : L % 2 = 1) :
    (realPolynomialEvenPart P).natDegree ≤ L - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [realPolynomialEvenPart_coeff]
  by_cases hpar : n % 2 = 0
  · have hLn : L ≤ n := by omega
    rcases lt_or_eq_of_le hLn with hlt | rfl
    · simp [hpar, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlt)]
    · have : ¬ L % 2 = 0 := by omega
      exact False.elim (this hpar)
  · simp [hpar]

/-- If a polynomial has degree at most an even `L`, then its odd coefficient
part has degree at most `L - 1`. -/
theorem realPolynomialOddPart_natDegree_le_pred_of_even_bound (P : ℝ[X]) {L : ℕ}
    (hdegree : P.natDegree ≤ L) (hL : L % 2 = 0) :
    (realPolynomialOddPart P).natDegree ≤ L - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [realPolynomialOddPart_coeff]
  by_cases hpar : n % 2 = 1
  · have hLn : L ≤ n := by omega
    rcases lt_or_eq_of_le hLn with hlt | rfl
    · simp [hpar, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlt)]
    · have : ¬ L % 2 = 1 := by omega
      exact False.elim (this hpar)
  · simp [hpar]

/-- The even coefficient part is the average of `P(X)` and `P(-X)`. -/
theorem realPolynomialEvenPart_eq_half_add_comp_neg_X (P : ℝ[X]) :
    realPolynomialEvenPart P =
      Polynomial.C ((2 : ℝ)⁻¹) * (P + P.comp (-Polynomial.X)) := by
  ext n
  rw [realPolynomialEvenPart_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_add]
  rw [show (-Polynomial.X : ℝ[X]) = Polynomial.C (-1 : ℝ) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases h : n % 2 = 0
  · have hEven : Even n := Nat.even_iff.mpr h
    simp [h, hEven.neg_one_pow]
    ring
  · have hOdd : Odd n := by
      rw [Nat.odd_iff]
      omega
    have hpow : (-1 : ℝ) ^ n = -1 := by
      simpa using hOdd.neg_one_pow
    simp [h, hpow]

/-- The odd coefficient part is half of `P(X) - P(-X)`. -/
theorem realPolynomialOddPart_eq_half_sub_comp_neg_X (P : ℝ[X]) :
    realPolynomialOddPart P =
      Polynomial.C ((2 : ℝ)⁻¹) * (P - P.comp (-Polynomial.X)) := by
  ext n
  rw [realPolynomialOddPart_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  rw [show (-Polynomial.X : ℝ[X]) = Polynomial.C (-1 : ℝ) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases h : n % 2 = 1
  · have hOdd : Odd n := by
      rw [Nat.odd_iff]
      exact h
    have hpow : (-1 : ℝ) ^ n = -1 := by
      simpa using hOdd.neg_one_pow
    simp [h, hpow]
    ring
  · have hEven : Even n := by
      rw [Nat.even_iff]
      omega
    simp [h, hEven.neg_one_pow]

/-- Evaluation of the even coefficient part. -/
theorem realPolynomialEvenPart_eval (P : ℝ[X]) (x : ℝ) :
    (realPolynomialEvenPart P).eval x = (P.eval x + P.eval (-x)) / 2 := by
  rw [realPolynomialEvenPart_eq_half_add_comp_neg_X]
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp]
  ring

/-- Evaluation of the odd coefficient part. -/
theorem realPolynomialOddPart_eval (P : ℝ[X]) (x : ℝ) :
    (realPolynomialOddPart P).eval x = (P.eval x - P.eval (-x)) / 2 := by
  rw [realPolynomialOddPart_eq_half_sub_comp_neg_X]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_comp]
  ring

/-- The complex even coefficient part is half of `P(X) + P(-X)`. -/
theorem complexPolynomialEvenPart_eq_half_add_comp_neg_X (P : ℂ[X]) :
    complexPolynomialEvenPart P =
      Polynomial.C ((2 : ℂ)⁻¹) * (P + P.comp (-Polynomial.X)) := by
  ext n
  rw [complexPolynomialEvenPart_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_add]
  rw [show (-Polynomial.X : ℂ[X]) = Polynomial.C (-1 : ℂ) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases h : n % 2 = 0
  · have hEven : Even n := Nat.even_iff.mpr h
    simp [h, hEven.neg_one_pow]
    ring
  · have hOdd : Odd n := by
      rw [Nat.odd_iff]
      omega
    have hpow : (-1 : ℂ) ^ n = -1 := by
      simpa using hOdd.neg_one_pow
    simp [h, hpow]

/-- The complex odd coefficient part is half of `P(X) - P(-X)`. -/
theorem complexPolynomialOddPart_eq_half_sub_comp_neg_X (P : ℂ[X]) :
    complexPolynomialOddPart P =
      Polynomial.C ((2 : ℂ)⁻¹) * (P - P.comp (-Polynomial.X)) := by
  ext n
  rw [complexPolynomialOddPart_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  rw [show (-Polynomial.X : ℂ[X]) = Polynomial.C (-1 : ℂ) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases h : n % 2 = 1
  · have hOdd : Odd n := by
      rw [Nat.odd_iff]
      exact h
    have hpow : (-1 : ℂ) ^ n = -1 := by
      simpa using hOdd.neg_one_pow
    simp [h, hpow]
    ring
  · have hEven : Even n := by
      rw [Nat.even_iff]
      omega
    simp [h, hEven.neg_one_pow]

/-- Evaluation of the complex even coefficient part. -/
theorem complexPolynomialEvenPart_eval (P : ℂ[X]) (z : ℂ) :
    (complexPolynomialEvenPart P).eval z = (P.eval z + P.eval (-z)) / 2 := by
  rw [complexPolynomialEvenPart_eq_half_add_comp_neg_X]
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_comp]
  ring

/-- Evaluation of the complex odd coefficient part. -/
theorem complexPolynomialOddPart_eval (P : ℂ[X]) (z : ℂ) :
    (complexPolynomialOddPart P).eval z = (P.eval z - P.eval (-z)) / 2 := by
  rw [complexPolynomialOddPart_eq_half_sub_comp_neg_X]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_comp]
  ring

/-- If a complex polynomial is bounded by `normSq <= 1` on `[-1,1]`, so is its
even coefficient part. -/
theorem complexPolynomialEvenPart_normSq_le_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq ((complexPolynomialEvenPart P).eval (x : ℂ)) ≤ 1 := by
  intro x hx
  have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  rw [complexPolynomialEvenPart_eval]
  have hxnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hP x hx
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  have hnegnorm : ‖P.eval (-(x : ℂ))‖ ≤ 1 := by
    have hsq : ‖P.eval (-(x : ℂ))‖ ^ 2 ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hP (-x) hneg
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (-(x : ℂ))))] at hsq
  have htri : ‖P.eval (x : ℂ) + P.eval (-(x : ℂ))‖ ≤
      ‖P.eval (x : ℂ)‖ + ‖P.eval (-(x : ℂ))‖ :=
    norm_add_le _ _
  have hdiv : ‖(P.eval (x : ℂ) + P.eval (-(x : ℂ))) / 2‖ =
      ‖P.eval (x : ℂ) + P.eval (-(x : ℂ))‖ / 2 := by
    rw [norm_div]
    norm_num
  have hnorm : ‖(P.eval (x : ℂ) + P.eval (-(x : ℂ))) / 2‖ ≤ 1 := by
    rw [hdiv]
    nlinarith [htri, hxnorm, hnegnorm,
      norm_nonneg (P.eval (x : ℂ) + P.eval (-(x : ℂ)))]
  rw [Complex.normSq_eq_norm_sq]
  rw [sq_le_one_iff₀ (norm_nonneg ((P.eval (x : ℂ) + P.eval (-(x : ℂ))) / 2))]
  exact hnorm

/-- If a complex polynomial is bounded by `normSq <= 1` on `[-1,1]`, so is its
odd coefficient part. -/
theorem complexPolynomialOddPart_normSq_le_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq ((complexPolynomialOddPart P).eval (x : ℂ)) ≤ 1 := by
  intro x hx
  have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  rw [complexPolynomialOddPart_eval]
  have hxnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hP x hx
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  have hnegnorm : ‖P.eval (-(x : ℂ))‖ ≤ 1 := by
    have hsq : ‖P.eval (-(x : ℂ))‖ ^ 2 ≤ 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hP (-x) hneg
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (-(x : ℂ))))] at hsq
  have htri : ‖P.eval (x : ℂ) - P.eval (-(x : ℂ))‖ ≤
      ‖P.eval (x : ℂ)‖ + ‖P.eval (-(x : ℂ))‖ := by
    simpa [sub_eq_add_neg] using norm_add_le (P.eval (x : ℂ)) (-(P.eval (-(x : ℂ))))
  have hdiv : ‖(P.eval (x : ℂ) - P.eval (-(x : ℂ))) / 2‖ =
      ‖P.eval (x : ℂ) - P.eval (-(x : ℂ))‖ / 2 := by
    rw [norm_div]
    norm_num
  have hnorm : ‖(P.eval (x : ℂ) - P.eval (-(x : ℂ))) / 2‖ ≤ 1 := by
    rw [hdiv]
    nlinarith [htri, hxnorm, hnegnorm,
      norm_nonneg (P.eval (x : ℂ) - P.eval (-(x : ℂ)))]
  rw [Complex.normSq_eq_norm_sq]
  rw [sq_le_one_iff₀ (norm_nonneg ((P.eval (x : ℂ) - P.eval (-(x : ℂ))) / 2))]
  exact hnorm

/-- If a real polynomial is bounded by one on `[-1,1]`, so is its even
coefficient part. -/
theorem realPolynomialEvenPart_boundedByOne_of_boundedByOne (P : ℝ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |(realPolynomialEvenPart P).eval x| ≤ 1 := by
  intro x hx
  have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  rw [realPolynomialEvenPart_eval]
  have htri :
      |P.eval x + P.eval (-x)| ≤ |P.eval x| + |P.eval (-x)| :=
    abs_add_le _ _
  have hdiv :
      |(P.eval x + P.eval (-x)) / 2| =
        |P.eval x + P.eval (-x)| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hdiv]
  nlinarith [htri, hP x hx, hP (-x) hneg, abs_nonneg (P.eval x),
    abs_nonneg (P.eval (-x)), abs_nonneg (P.eval x + P.eval (-x))]

/-- If a real polynomial is bounded by one on `[-1,1]`, so is its odd
coefficient part. -/
theorem realPolynomialOddPart_boundedByOne_of_boundedByOne (P : ℝ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |(realPolynomialOddPart P).eval x| ≤ 1 := by
  intro x hx
  have hneg : -x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  rw [realPolynomialOddPart_eval]
  have htri :
      |P.eval x - P.eval (-x)| ≤ |P.eval x| + |P.eval (-x)| := by
    simpa [sub_eq_add_neg] using abs_add_le (P.eval x) (-(P.eval (-x)))
  have hdiv :
      |(P.eval x - P.eval (-x)) / 2| =
        |P.eval x - P.eval (-x)| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hdiv]
  nlinarith [htri, hP x hx, hP (-x) hneg, abs_nonneg (P.eval x),
    abs_nonneg (P.eval (-x)), abs_nonneg (P.eval x - P.eval (-x))]

/-- A complex polynomial bounded by `normSq <= 1` has coefficientwise real part
bounded by one on the real unit interval. -/
theorem complexPolynomialRealPart_boundedByOne_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |(complexPolynomialRealPart P).eval x| ≤ 1 := by
  intro x hx
  rw [complexPolynomialRealPart_eval_ofReal]
  have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hP x hx
  have hnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  exact (Complex.abs_re_le_norm (P.eval (x : ℂ))).trans hnorm

/-- A complex polynomial bounded by `normSq <= 1` has coefficientwise imaginary
part bounded by one on the real unit interval. -/
theorem complexPolynomialImagPart_boundedByOne_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |(complexPolynomialImagPart P).eval x| ≤ 1 := by
  intro x hx
  rw [complexPolynomialImagPart_eval_ofReal]
  have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hP x hx
  have hnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  exact (Complex.abs_im_le_norm (P.eval (x : ℂ))).trans hnorm

/-- Scaling a norm-bounded complex polynomial by `1/4` makes its real part
bounded by `1/2` on the real unit interval.  This is the elementary bound used
by the complex-polynomial note after `thm:arbParity`
[GSLW19, BlockHam.tex:1952]. -/
theorem complexPolynomialRealPart_quarter_boundedByHalf_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |(complexPolynomialRealPart (Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P)).eval x|
        ≤ (1 / 2 : ℝ) := by
  intro x hx
  rw [complexPolynomialRealPart_eval_ofReal]
  have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hP x hx
  have hnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  have hscale :
      ‖(Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖(Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ)‖ =
          ‖(((4 : ℝ)⁻¹ : ℂ) * P.eval (x : ℂ))‖ := by simp
      _ = ‖(((4 : ℝ)⁻¹ : ℂ))‖ * ‖P.eval (x : ℂ)‖ := by
          rw [norm_mul]
      _ = (1 / 4 : ℝ) * ‖P.eval (x : ℂ)‖ := by norm_num
      _ ≤ (1 / 4 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
      _ = (1 / 4 : ℝ) := by norm_num
  exact (Complex.abs_re_le_norm
    ((Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ))).trans
      (hscale.trans (by norm_num))

/-- Scaling a norm-bounded complex polynomial by `1/4` makes its imaginary part
bounded by `1/2` on the real unit interval.  This is the elementary bound used
by the complex-polynomial note after `thm:arbParity`
[GSLW19, BlockHam.tex:1952]. -/
theorem complexPolynomialImagPart_quarter_boundedByHalf_of_normSq_le (P : ℂ[X])
    (hP : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |(complexPolynomialImagPart (Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P)).eval x|
        ≤ (1 / 2 : ℝ) := by
  intro x hx
  rw [complexPolynomialImagPart_eval_ofReal]
  have hsq : ‖P.eval (x : ℂ)‖ ^ 2 ≤ 1 := by
    simpa [Complex.normSq_eq_norm_sq] using hP x hx
  have hnorm : ‖P.eval (x : ℂ)‖ ≤ 1 := by
    rwa [sq_le_one_iff₀ (norm_nonneg (P.eval (x : ℂ)))] at hsq
  have hscale :
      ‖(Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    calc
      ‖(Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ)‖ =
          ‖(((4 : ℝ)⁻¹ : ℂ) * P.eval (x : ℂ))‖ := by simp
      _ = ‖(((4 : ℝ)⁻¹ : ℂ))‖ * ‖P.eval (x : ℂ)‖ := by
          rw [norm_mul]
      _ = (1 / 4 : ℝ) * ‖P.eval (x : ℂ)‖ := by norm_num
      _ ≤ (1 / 4 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hnorm (by norm_num)
      _ = (1 / 4 : ℝ) := by norm_num
  exact (Complex.abs_im_le_norm
    ((Polynomial.C (((4 : ℝ)⁻¹ : ℂ)) * P).eval (x : ℂ))).trans
      (hscale.trans (by norm_num))

/-- Complex polynomials split into real/imaginary and even/odd coefficient
parts. -/
theorem complexPolynomial_fourPart_recompose (P : ℂ[X]) :
    realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialRealPart P)) +
        realPolynomialToComplex (realPolynomialOddPart (complexPolynomialRealPart P)) +
        (Polynomial.C Complex.I *
          realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialImagPart P)) +
        Polynomial.C Complex.I *
          realPolynomialToComplex (realPolynomialOddPart (complexPolynomialImagPart P))) = P := by
  have hre := congrArg realPolynomialToComplex
    (realPolynomial_evenPart_add_oddPart (complexPolynomialRealPart P))
  have him := congrArg realPolynomialToComplex
    (realPolynomial_evenPart_add_oddPart (complexPolynomialImagPart P))
  rw [realPolynomialToComplex_add] at hre him
  calc
    realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialRealPart P)) +
          realPolynomialToComplex (realPolynomialOddPart (complexPolynomialRealPart P)) +
          (Polynomial.C Complex.I *
            realPolynomialToComplex (realPolynomialEvenPart (complexPolynomialImagPart P)) +
          Polynomial.C Complex.I *
            realPolynomialToComplex (realPolynomialOddPart (complexPolynomialImagPart P)))
        = realPolynomialToComplex (complexPolynomialRealPart P) +
            Polynomial.C Complex.I *
              realPolynomialToComplex (complexPolynomialImagPart P) := by
          rw [← hre, ← him]
          ring
    _ = P := complexPolynomial_recompose P

@[simp]
theorem realPolynomialToComplex_degree (P : ℝ[X]) :
    (realPolynomialToComplex P).degree = P.degree := by
  simpa [realPolynomialToComplex] using
    (Polynomial.degree_map_eq_of_injective
      (f := (algebraMap ℝ ℂ)) Complex.ofReal_injective P)

@[simp]
theorem realPolynomialToComplex_natDegree (P : ℝ[X]) :
    (realPolynomialToComplex P).natDegree = P.natDegree := by
  simpa [realPolynomialToComplex] using
    (Polynomial.natDegree_map_eq_of_injective
      (f := (algebraMap ℝ ℂ)) Complex.ofReal_injective P)

/-- Complexifying a real polynomial does not change the multiplicity of a real
root. -/
theorem realPolynomialToComplex_rootMultiplicity_ofReal (P : ℝ[X]) (x : ℝ) :
    P.rootMultiplicity x =
      (realPolynomialToComplex P).rootMultiplicity (x : ℂ) := by
  simpa [realPolynomialToComplex] using
    (Polynomial.eq_rootMultiplicity_map
      (p := P) (f := (algebraMap ℝ ℂ)) Complex.ofReal_injective x)

/-! ### Coefficient-conjugate polynomials -/

/-- `conjP P` conjugates every coefficient of `P : ℂ[X]`; this is the `P*` of
the QSP literature (for real `x`, `(conjP P).eval x = conj (P.eval x)`). -/
noncomputable def conjP (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)

@[simp]
theorem conjP_coeff (P : ℂ[X]) (k : ℕ) :
    (conjP P).coeff k = starRingEnd ℂ (P.coeff k) :=
  Polynomial.coeff_map _ _

@[simp] theorem conjP_zero : conjP 0 = 0 := Polynomial.map_zero _

@[simp] theorem conjP_one : conjP 1 = 1 := Polynomial.map_one _

@[simp] theorem conjP_X : conjP X = X := Polynomial.map_X _

@[simp]
theorem conjP_C (c : ℂ) : conjP (C c) = C (starRingEnd ℂ c) :=
  Polynomial.map_C _

theorem conjP_add (P Q : ℂ[X]) : conjP (P + Q) = conjP P + conjP Q :=
  Polynomial.map_add _

theorem conjP_sub (P Q : ℂ[X]) : conjP (P - Q) = conjP P - conjP Q :=
  Polynomial.map_sub _

theorem conjP_mul (P Q : ℂ[X]) : conjP (P * Q) = conjP P * conjP Q :=
  Polynomial.map_mul _

theorem conjP_pow (P : ℂ[X]) (n : ℕ) : conjP (P ^ n) = conjP P ^ n :=
  Polynomial.map_pow _ _

@[simp]
theorem conjP_conjP (P : ℂ[X]) : conjP (conjP P) = P := by
  ext k
  simp

@[simp]
theorem conjP_realPolynomialToComplex (P : ℝ[X]) :
    conjP (realPolynomialToComplex P) = realPolynomialToComplex P := by
  ext k
  simp [conjP_coeff, realPolynomialToComplex, Complex.conj_ofReal]

theorem realPolynomialToComplex_mul_conjP (P : ℝ[X]) :
    realPolynomialToComplex P * conjP (realPolynomialToComplex P) =
      realPolynomialToComplex (P ^ 2) := by
  simp [pow_two]

theorem conjP_realPolynomialToComplex_mul (P : ℝ[X]) :
    conjP (realPolynomialToComplex P) * realPolynomialToComplex P =
      realPolynomialToComplex (P ^ 2) := by
  simp [pow_two]

/-- Evaluating the coefficient-conjugate at a real point conjugates the value. -/
theorem conjP_eval_ofReal (P : ℂ[X]) (x : ℝ) :
    (conjP P).eval (x : ℂ) = starRingEnd ℂ (P.eval (x : ℂ)) := by
  have h : ((x : ℂ)) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  rw [conjP, Polynomial.eval_map]
  conv_lhs => rw [h]
  rw [Polynomial.eval₂_hom]

/-- Evaluating the coefficient-conjugate at the conjugate point conjugates the
original value. -/
theorem conjP_eval_conj (P : ℂ[X]) (z : ℂ) :
    (conjP P).eval (starRingEnd ℂ z) = starRingEnd ℂ (P.eval z) := by
  rw [conjP, Polynomial.eval_map, Polynomial.eval₂_hom]

/-! ### Parity of polynomials

`HasParity P p` says every nonzero coefficient of `P` sits in a degree
congruent to `p` modulo `2` ("`P` has parity `p mod 2`" in
[Lin22, hermfunc.tex:1132]). The zero polynomial has every parity. -/

/-- All nonzero coefficients of `P` are in degrees `≡ p (mod 2)`. -/
def HasParity (P : ℂ[X]) (p : ℕ) : Prop :=
  ∀ k, P.coeff k ≠ 0 → k % 2 = p % 2

theorem HasParity.coeff_eq_zero {P : ℂ[X]} {p : ℕ} (h : HasParity P p) {k : ℕ}
    (hk : k % 2 ≠ p % 2) : P.coeff k = 0 :=
  by_contra fun hne => hk (h k hne)

theorem hasParity_zero (p : ℕ) : HasParity 0 p := fun k hk => by simp at hk

theorem hasParity_C (c : ℂ) {p : ℕ} (hp : p % 2 = 0) : HasParity (C c) p := by
  intro k hk
  rw [Polynomial.coeff_C] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [hp]
  · simp [Nat.pos_iff_ne_zero.mp hpos] at hk

theorem HasParity.add {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P + Q) p := by
  intro k hk
  rw [Polynomial.coeff_add] at hk
  by_cases h : P.coeff k = 0
  · exact hQ k (by simpa [h] using hk)
  · exact hP k h

theorem HasParity.neg {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (-P) p := by
  intro k hk
  rw [Polynomial.coeff_neg, neg_ne_zero] at hk
  exact hP k hk

theorem HasParity.sub {P Q : ℂ[X]} {p : ℕ} (hP : HasParity P p)
    (hQ : HasParity Q p) : HasParity (P - Q) p := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

theorem HasParity.C_mul {P : ℂ[X]} {p : ℕ} (c : ℂ) (hP : HasParity P p) :
    HasParity (C c * P) p := by
  intro k hk
  rw [Polynomial.coeff_C_mul] at hk
  exact hP k (right_ne_zero_of_mul hk)

theorem HasParity.conjP {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (conjP P) p := by
  intro k hk
  rw [conjP_coeff] at hk
  exact hP k fun h => hk (by simp [h])

/-- Parity only depends on `p` modulo `2`. -/
theorem HasParity.congr {P : ℂ[X]} {p q : ℕ} (hP : HasParity P p)
    (hpq : p % 2 = q % 2) : HasParity P q := by
  intro k hk
  rw [hP k hk, hpq]

theorem realPolynomialEvenPart_hasParity (P : ℝ[X]) :
    HasParity (realPolynomialToComplex (realPolynomialEvenPart P)) 0 := by
  intro n hn
  rw [realPolynomialToComplex, Polynomial.coeff_map] at hn
  by_contra hpar
  have hzero : (realPolynomialEvenPart P).coeff n = 0 := by
    simp [hpar]
  simp [hzero] at hn

theorem realPolynomialOddPart_hasParity (P : ℝ[X]) :
    HasParity (realPolynomialToComplex (realPolynomialOddPart P)) 1 := by
  intro n hn
  rw [realPolynomialToComplex, Polynomial.coeff_map] at hn
  by_contra hpar
  have hzero : (realPolynomialOddPart P).coeff n = 0 := by
    simp [hpar]
  simp [hzero] at hn

theorem complexPolynomialEvenPart_hasParity (P : ℂ[X]) :
    HasParity (complexPolynomialEvenPart P) 0 := by
  intro n hn
  rw [complexPolynomialEvenPart_coeff] at hn
  by_cases h : n % 2 = 0
  · simp [h]
  · simp [h] at hn

theorem complexPolynomialOddPart_hasParity (P : ℂ[X]) :
    HasParity (complexPolynomialOddPart P) 1 := by
  intro n hn
  rw [complexPolynomialOddPart_coeff] at hn
  by_cases h : n % 2 = 1
  · simp [h]
  · simp [h] at hn

/-- Total coefficient formula for `X * P`. -/
theorem coeff_X_mul' (P : ℂ[X]) (n : ℕ) :
    (X * P).coeff n = if n = 0 then 0 else P.coeff (n - 1) := by
  cases n with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ m => simp [Polynomial.coeff_X_mul]

/-- Total coefficient formula for `X^2 * P`. -/
theorem coeff_X_sq_mul (P : ℂ[X]) (n : ℕ) :
    (X ^ 2 * P).coeff n = if n < 2 then 0 else P.coeff (n - 2) := by
  have h : (X ^ 2 * P : ℂ[X]) = X * (X * P) := by ring
  rw [h, coeff_X_mul' (X * P) n]
  rcases n with - | m
  · simp
  · rw [if_neg (Nat.succ_ne_zero m), Nat.succ_sub_one, coeff_X_mul' P m]
    rcases m with - | l
    · simp
    · have h1 : ¬ (l + 2 < 2) := by omega
      have h2 : l + 2 - 2 = l + 1 - 1 := by omega
      simp [h1, h2]

theorem HasParity.X_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity (X * P) (p + 1) := by
  intro k hk
  rw [coeff_X_mul'] at hk
  by_cases hk0 : k = 0
  · simp [hk0] at hk
  · rw [if_neg hk0] at hk
    have := hP _ hk
    omega

theorem HasParity.one_sub_X_sq_mul {P : ℂ[X]} {p : ℕ} (hP : HasParity P p) :
    HasParity ((1 - X ^ 2) * P) p := by
  have h : ((1 - X ^ 2) * P : ℂ[X]) = P - X ^ 2 * P := by ring
  rw [h]
  refine hP.sub ?_
  intro k hk
  rw [coeff_X_sq_mul] at hk
  by_cases hk2 : k < 2
  · simp [hk2] at hk
  · rw [if_neg hk2] at hk
    have := hP _ hk
    omega

/-! ### Square-variable parity quotients -/

/-- Even-degree coefficient quotient: `P(X)` is read as a polynomial in
`X^2` by keeping the coefficients in degrees `2k`.

This is a quantum-free helper for QSP/QSVT parity arguments.  The source-facing
QSVT notation `P^{(SV)}` separates even and odd polynomials in exactly this
way before applying the polynomial to singular values [GSLW19,
BlockHam.tex:747-764]. -/
noncomputable def evenSquareQuotient (P : ℂ[X]) : ℂ[X] :=
  P.sum fun n a => if n % 2 = 0 then C a * X ^ (n / 2) else 0

@[simp]
theorem evenSquareQuotient_one : evenSquareQuotient (1 : ℂ[X]) = 1 := by
  have hsupp : (1 : ℂ[X]).support = {0} := by
    simpa using (Polynomial.support_C (R := ℂ) (a := (1 : ℂ)) one_ne_zero)
  rw [evenSquareQuotient, Polynomial.sum_def, hsupp]
  simp

theorem evenSquareQuotient_add (P Q : ℂ[X]) :
    evenSquareQuotient (P + Q) = evenSquareQuotient P + evenSquareQuotient Q := by
  rw [evenSquareQuotient, evenSquareQuotient, evenSquareQuotient,
    Polynomial.sum_add_index]
  · intro i
    by_cases h : i % 2 = 0 <;> simp [h]
  · intro i a b
    by_cases h : i % 2 = 0 <;> simp [h, Polynomial.C_add, add_mul]

theorem evenSquareQuotient_smul (c : ℂ) (P : ℂ[X]) :
    evenSquareQuotient (c • P) = c • evenSquareQuotient P := by
  rw [evenSquareQuotient, evenSquareQuotient, Polynomial.sum_smul_index]
  · simp [Polynomial.smul_sum, Polynomial.smul_eq_C_mul, mul_assoc]
  · intro i
    by_cases h : i % 2 = 0 <;> simp [h]

/-- Odd-degree coefficient quotient: `P(X) = X * Q(X^2)` for the coefficients
in degrees `2k+1`, when `P` has odd parity.  This is the odd counterpart of
`evenSquareQuotient` for the source notation `P^{(SV)}` [GSLW19,
BlockHam.tex:747-764]. -/
noncomputable def oddSquareQuotient (P : ℂ[X]) : ℂ[X] :=
  P.sum fun n a => if n % 2 = 1 then C a * X ^ ((n - 1) / 2) else 0

@[simp]
theorem oddSquareQuotient_X : oddSquareQuotient (X : ℂ[X]) = 1 := by
  rw [oddSquareQuotient, Polynomial.sum_X_index]
  · norm_num
  · simp

theorem oddSquareQuotient_add (P Q : ℂ[X]) :
    oddSquareQuotient (P + Q) = oddSquareQuotient P + oddSquareQuotient Q := by
  rw [oddSquareQuotient, oddSquareQuotient, oddSquareQuotient,
    Polynomial.sum_add_index]
  · intro i
    by_cases h : i % 2 = 1 <;> simp [h]
  · intro i a b
    by_cases h : i % 2 = 1 <;> simp [h, Polynomial.C_add, add_mul]

theorem oddSquareQuotient_smul (c : ℂ) (P : ℂ[X]) :
    oddSquareQuotient (c • P) = c • oddSquareQuotient P := by
  rw [oddSquareQuotient, oddSquareQuotient, Polynomial.sum_smul_index]
  · simp [Polynomial.smul_sum, Polynomial.smul_eq_C_mul, mul_assoc]
  · intro i
    by_cases h : i % 2 = 1 <;> simp [h]

/-- Substituting `X^2` into the even square quotient recovers an even-parity
polynomial.  This is the coefficient-level calculation behind the even branch
of `P^{(SV)}` in the QSVT singular-value transform [GSLW19,
BlockHam.tex:747-764]. -/
theorem evenSquareQuotient_eval_sq_of_hasParity {P : Polynomial Complex}
    {parity : Nat} (hpar : parity % 2 = 0) (hP : HasParity P parity)
    (x : Complex) :
    (evenSquareQuotient P).eval (x ^ 2) = P.eval x := by
  rw [evenSquareQuotient, Polynomial.eval_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Polynomial.sum_def]
  refine Finset.sum_congr rfl ?_
  intro n ha
  by_cases hn : n % 2 = 0
  case pos =>
    have hpow : (x ^ 2) ^ (n / 2) = x ^ n := by
      have hn2 : 2 * (n / 2) = n := by omega
      calc
        (x ^ 2) ^ (n / 2) = x ^ (2 * (n / 2)) := by rw [pow_mul]
        _ = x ^ n := by rw [hn2]
    simp [hn, hpow]
  case neg =>
    have hcoeff_zero : P.coeff n = 0 := by
      have hnpar : n % 2 ≠ parity % 2 := by
        rw [hpar]
        exact hn
      exact hP.coeff_eq_zero hnpar
    have hn_not_mem : n ∉ P.support := by
      simp [Polynomial.mem_support_iff, hcoeff_zero]
    exact False.elim (hn_not_mem ha)

/-- Substituting `X^2` into the odd square quotient recovers an odd-parity
polynomial after the leading factor `X`.  This is the coefficient-level
calculation behind the odd branch of `P^{(SV)}` [GSLW19,
BlockHam.tex:747-764]. -/
theorem oddSquareQuotient_eval_sq_of_hasParity {P : Polynomial Complex}
    {parity : Nat} (hpar : parity % 2 = 1) (hP : HasParity P parity)
    (x : Complex) :
    x * (oddSquareQuotient P).eval (x ^ 2) = P.eval x := by
  rw [oddSquareQuotient, Polynomial.eval_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def, Polynomial.sum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n ha
  by_cases hn : n % 2 = 1
  case pos =>
    have hpow : x * (x ^ 2) ^ ((n - 1) / 2) = x ^ n := by
      have hn2 : 2 * ((n - 1) / 2) + 1 = n := by omega
      calc
        x * (x ^ 2) ^ ((n - 1) / 2)
            = x * x ^ (2 * ((n - 1) / 2)) := by rw [pow_mul]
        _ = x ^ (2 * ((n - 1) / 2) + 1) := by
          rw [pow_succ]
          rw [mul_comm]
        _ = x ^ n := by rw [hn2]
    rw [if_pos hn]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    calc
      x * (P.coeff n * (x ^ 2) ^ ((n - 1) / 2))
          = P.coeff n * (x * (x ^ 2) ^ ((n - 1) / 2)) := by ring
      _ = P.coeff n * x ^ n := by rw [hpow]
  case neg =>
    have hcoeff_zero : P.coeff n = 0 := by
      have hnpar : n % 2 ≠ parity % 2 := by
        rw [hpar]
        exact hn
      exact hP.coeff_eq_zero hnpar
    have hn_not_mem : n ∉ P.support := by
      simp [Polynomial.mem_support_iff, hcoeff_zero]
    exact False.elim (hn_not_mem ha)

/-- Polynomial identity form of `evenSquareQuotient_eval_sq_of_hasParity`:
an even-parity polynomial is obtained by substituting `X^2` into its quotient.
This is the algebraic form used by Hermitian QSVT specialization
[GSLW19, BlockHam.tex:747-764]. -/
theorem evenSquareQuotient_comp_X_sq_of_hasParity {P : Polynomial Complex}
    {parity : Nat} (hpar : parity % 2 = 0) (hP : HasParity P parity) :
    (evenSquareQuotient P).comp (Polynomial.X ^ 2) = P := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  exact evenSquareQuotient_eval_sq_of_hasParity hpar hP x

/-- Polynomial identity form of `oddSquareQuotient_eval_sq_of_hasParity`:
an odd-parity polynomial is `X` times a polynomial in `X^2`.
This is the algebraic form used by Hermitian QSVT specialization
[GSLW19, BlockHam.tex:747-764]. -/
theorem oddSquareQuotient_comp_X_sq_of_hasParity {P : Polynomial Complex}
    {parity : Nat} (hpar : parity % 2 = 1) (hP : HasParity P parity) :
    Polynomial.X * (oddSquareQuotient P).comp (Polynomial.X ^ 2) = P := by
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact oddSquareQuotient_eval_sq_of_hasParity hpar hP x

/-! ### Bounded product coefficients -/

/-- Product coefficient at the sum of two coefficient bounds: only the
top-times-top term survives. -/
theorem coeff_mul_at_bound_add {P Q : ℂ[X]} {a b n : ℕ} (hn : n = a + b)
    (hP : ∀ m, a < m → P.coeff m = 0) (hQ : ∀ m, b < m → Q.coeff m = 0) :
    (P * Q).coeff n = P.coeff a * Q.coeff b := by
  subst hn
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single_of_mem (a, b)
    (Finset.mem_antidiagonal.mpr rfl) (fun c hc hne => ?_)
  rw [Finset.mem_antidiagonal] at hc
  rcases lt_or_ge a c.1 with h1 | h1
  · rw [hP c.1 h1, zero_mul]
  · have h2 : b < c.2 := by
      rcases lt_or_ge b c.2 with h | h
      · exact h
      · exact absurd (Prod.ext (by omega) (by omega)) hne
    rw [hQ c.2 h2, mul_zero]

/-- Product coefficient above the sum of two coefficient bounds vanishes. -/
theorem coeff_mul_eq_zero_of_bound_add {P Q : ℂ[X]} {a b n : ℕ}
    (hn : a + b < n)
    (hP : ∀ m, a < m → P.coeff m = 0) (hQ : ∀ m, b < m → Q.coeff m = 0) :
    (P * Q).coeff n = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [Finset.mem_antidiagonal] at hc
  rcases lt_or_ge a c.1 with h1 | h1
  · rw [hP c.1 h1, zero_mul]
  · rw [hQ c.2 (by omega), mul_zero]

/-! ### Reflection of coefficients -/

theorem coeff_reflect_of_le {F : ℂ[X]} {N m : ℕ} (hm : m ≤ N) :
    (F.reflect N).coeff m = F.coeff (N - m) := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le hm]

theorem coeff_reflect_eq_zero {F : ℂ[X]} {N m : ℕ} (hF : F.natDegree ≤ N)
    (hm : N < m) : (F.reflect N).coeff m = 0 := by
  rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hm]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF hm)

theorem reflect_sub (F G : ℂ[X]) (N : ℕ) :
    (F - G).reflect N = F.reflect N - G.reflect N := by
  ext k
  simp [Polynomial.coeff_reflect]

theorem reflect_add' (F G : ℂ[X]) (N : ℕ) :
    (F + G).reflect N = F.reflect N + G.reflect N := by
  ext k
  simp [Polynomial.coeff_reflect]

/-- `reflect (L+1) F = X · reflect L F` for `natDegree F ≤ L`. -/
theorem reflect_succ {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    F.reflect (L + 1) = X * F.reflect L := by
  ext k
  rw [Polynomial.coeff_reflect, coeff_X_mul']
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [if_pos rfl, Polynomial.revAt_le (Nat.zero_le _)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge k (L + 2) with hk2 | hk2
    · rw [Polynomial.revAt_le (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_le (by omega)]
      congr 1
      omega
    · rw [Polynomial.revAt_eq_self_of_lt (by omega), Polynomial.coeff_reflect,
        Polynomial.revAt_eq_self_of_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Increasing a reflection budget only adds leading powers of `X`. -/
theorem reflect_add_budget {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) (d : ℕ) :
    F.reflect (L + d) = X ^ d * F.reflect L := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hF' : F.natDegree ≤ L + d := by omega
      rw [show L + (d + 1) = (L + d) + 1 by omega]
      rw [reflect_succ hF', ih]
      simp [pow_succ, mul_assoc, mul_comm]

/-- `reflect (L+1) (X·F) = reflect L F` for `natDegree F ≤ L`. -/
theorem reflect_X_mul {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) :
    (X * F).reflect (L + 1) = F.reflect L := by
  rw [show L + 1 = 1 + L by omega]
  rw [Polynomial.reflect_mul (X : ℂ[X]) F (by simp) hF]
  rw [Polynomial.reflect_one_X, one_mul]

/-- Evaluation of a reflection: `(reflect L F)(z) = z^L · F(z⁻¹)`. -/
theorem eval_reflect {F : ℂ[X]} {L : ℕ} (hF : F.natDegree ≤ L) {z : ℂ}
    (hz : z ≠ 0) : (F.reflect L).eval z = z ^ L * F.eval z⁻¹ := by
  have h1 : (F.reflect L).natDegree ≤ L :=
    Polynomial.natDegree_le_iff_degree_le.mpr <|
      (Polynomial.degree_le_iff_coeff_zero _ _).mpr fun m hm =>
        coeff_reflect_eq_zero hF (by exact_mod_cast hm)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le h1),
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hF), Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [coeff_reflect_of_le (by omega), show L - (L + 1 - 1 - k) = k by omega,
    show z ^ L = z ^ (L + 1 - 1 - k) * z ^ k by rw [← pow_add]; congr 1; omega,
    inv_pow]
  field_simp

theorem reflect_zero_C (r : ℂ) : (C r).reflect 0 = C r := by
  ext k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_le (le_refl 0)]
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_eq_self_of_lt hk]

/-! ### Evaluation on the unit circle -/

/-- Two polynomials agreeing on the unit circle are equal (the circle is an
infinite evaluation set). -/
theorem eq_of_circle_eval_eq {F G : ℂ[X]}
    (h : ∀ x : ℝ, F.eval (Complex.exp ((x : ℂ) * Complex.I))
      = G.eval (Complex.exp ((x : ℂ) * Complex.I))) : F = G := by
  refine Polynomial.eq_of_infinite_eval_eq F G ?_
  refine ((Set.Ioo_infinite Real.pi_pos).image exp_I_injOn_Ioo).mono ?_
  rintro z ⟨x, _, rfl⟩
  exact h x

end QuantumAlg
