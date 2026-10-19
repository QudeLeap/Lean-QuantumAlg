/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic

/-!
# Real trigonometric form of a finite Fourier sum

The real part of a finite complex exponential sum with frequencies among
`0, ±1, …, ±R` is a real trigonometric polynomial of degree at most `R`.
Repeated and zero frequencies are collected by addition, without any distinctness
assumption on the individual summands.
-/

@[expose] public section

namespace Complex

open scoped BigOperators

noncomputable section

/-- Euler's identity for the real part of one Fourier summand. -/
lemma re_mul_exp_real_phase (c : ℂ) (y : ℝ) :
    (c * Complex.exp ((y : ℂ) * Complex.I)).re =
      c.re * Real.cos y - c.im * Real.sin y := by
  rw [Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]

private lemma sparse_trig_sum (A B : ℝ) (p R : ℕ)
    (hp : p ∈ Finset.Icc 1 R) (x : ℝ) :
    (if 0 = p then A else 0) +
        ∑ q ∈ Finset.Icc 1 R,
          ((if q = p then A else 0) * Real.cos ((q : ℝ) * x) +
            (if q = p then B else 0) * Real.sin ((q : ℝ) * x)) =
      A * Real.cos ((p : ℝ) * x) + B * Real.sin ((p : ℝ) * x) := by
  have hp0 : 0 ≠ p := by have := (Finset.mem_Icc.mp hp).1; omega
  rw [if_neg hp0, zero_add, Finset.sum_eq_single p]
  · simp
  · intro q _ hqp
    simp [hqp]
  · exact fun h => (h hp).elim

private lemma one_phase_has_trig (c : ℂ) (γ : ℝ) (R : ℕ)
    (hγ : γ = 0 ∨ ∃ p ∈ Finset.Icc 1 R, γ = (p : ℝ) ∨ γ = -(p : ℝ)) :
    ∃ a b : ℕ → ℝ, ∀ x : ℝ,
      (c * Complex.exp (((γ * x : ℝ) : ℂ) * Complex.I)).re =
        a 0 + ∑ p ∈ Finset.Icc 1 R,
          (a p * Real.cos ((p : ℝ) * x) + b p * Real.sin ((p : ℝ) * x)) := by
  rcases hγ with rfl | ⟨p, hp, hpos | hneg⟩
  · refine ⟨fun p => if p = 0 then c.re else 0, fun _ => 0, ?_⟩
    intro x
    simp only [zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one, add_zero]
    symm
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro p hp
    have hp0 : p ≠ 0 := by have := (Finset.mem_Icc.mp hp).1; omega
    simp [hp0]
  · refine ⟨fun q => if q = p then c.re else 0,
      fun q => if q = p then -c.im else 0, ?_⟩
    intro x
    rw [hpos, re_mul_exp_real_phase, sparse_trig_sum _ _ _ _ hp]
    ring
  · refine ⟨fun q => if q = p then c.re else 0,
      fun q => if q = p then c.im else 0, ?_⟩
    intro x
    rw [hneg, re_mul_exp_real_phase, sparse_trig_sum _ _ _ _ hp]
    simp only [neg_mul, Real.cos_neg, Real.sin_neg]
    ring

/-- Collect a finite list of signed integer frequencies into real cosine and sine coefficients.
The zero coefficient includes every zero-frequency summand, even when frequencies repeat. -/
lemma finite_integer_fourier_has_trig {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (γ : ι → ℝ) (R : ℕ)
    (hγ : ∀ i ∈ s, γ i = 0 ∨
      ∃ p ∈ Finset.Icc 1 R, γ i = (p : ℝ) ∨ γ i = -(p : ℝ)) :
    ∃ a b : ℕ → ℝ, ∀ x : ℝ,
      ∑ i ∈ s, (c i * Complex.exp ((((γ i) * x : ℝ) : ℂ) * Complex.I)).re =
        a 0 + ∑ p ∈ Finset.Icc 1 R,
          (a p * Real.cos ((p : ℝ) * x) + b p * Real.sin ((p : ℝ) * x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨fun _ => 0, fun _ => 0, fun _ => by simp⟩
  | @insert i s hi ih =>
      obtain ⟨a, b, hab⟩ := one_phase_has_trig (c i) (γ i) R
        (hγ i (Finset.mem_insert_self _ _))
      obtain ⟨a', b', hab'⟩ := ih (fun j hj => hγ j (Finset.mem_insert_of_mem hj))
      refine ⟨fun p => a p + a' p, fun p => b p + b' p, ?_⟩
      intro x
      rw [Finset.sum_insert hi, hab, hab']
      simp only [add_mul]
      simp_rw [Finset.sum_add_distrib]
      ring

end

end Complex
