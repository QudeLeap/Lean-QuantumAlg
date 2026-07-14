/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-!
# Finite trigonometric-sum (Dirichlet-kernel) identities (quantum-free)

The exact first- and second-derivative-at-the-origin rules for a real degree-`R`
trigonometric polynomial `ℓ(x) = a₀ + ∑_{p=1}^R (a_p cos(p x) + b_p sin(p x))`
are weighted sums of finitely many shifted evaluations. Proving those rules
reduces, by linearity in the coefficients, to a handful of scalar identities on
the equidistant node sets `(2μ-1)π/(2R)` (odd) and `μπ/R` (even). This module
develops those identities from scratch — Mathlib has no Dirichlet-kernel theory —
so they can be reused by the parameter-shift development without any quantum
dependency.

The engine is the modified Dirichlet kernel, packaged as an explicit degree-`R`
cosine polynomial
`D̃(x) = 1/(2R) + 1/(2R) cos(R x) + (1/R) ∑_{ℓ=1}^{R-1} cos(ℓ x)`,
whose derivatives at the nodes supply the `1/sin²` weights without ever summing
`1/sin²` directly.

## Main results

- `sum_sq_range` — the closed form `∑_{ℓ<R} ℓ² = R(R-1)(2R-1)/6`.
- the per-frequency node identities feeding the first/second derivative rules
  of Wierichs et al. [WIWL22, main.tex:482-484].
-/

@[expose] public section

namespace QuantumAlg

open scoped BigOperators

/-- Closed form for the finite sum of squares, `∑_{ℓ<R} ℓ² = R(R-1)(2R-1)/6`
(real-valued; the subtractions are over `ℝ`, so the `R = 0` case is `0`). Mathlib
provides the linear analogue but not this one. -/
theorem sum_sq_range (R : ℕ) :
    ∑ ℓ ∈ Finset.range R, (ℓ : ℝ) ^ 2 = (R : ℝ) * ((R : ℝ) - 1) * (2 * (R : ℝ) - 1) / 6 := by
  induction R with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Closed form for the same square sum over the interval `1 ≤ ℓ ≤ R - 1`. -/
theorem sum_sq_Icc_one_sub (R : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2
      = (R : ℝ) * ((R : ℝ) - 1) * (2 * (R : ℝ) - 1) / 6 := by
  induction R with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hn1 : 1 ≤ n := by omega
      rw [show n + 1 - 1 = n by omega]
      conv_lhs => rw [← show n - 1 + 1 = n by omega]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n - 1 + 1), show n - 1 + 1 = n by omega, ih]
      push_cast
      ring

/-! ### Equidistant nodes and weights

The first-derivative rule samples the `2R` odd nodes `x_μ = (2μ-1)π/(2R)`; the
second-derivative rule samples the `2R-1` even nodes `μπ/R`. The weights are the
node-derivatives of the modified Dirichlet kernel. -/

/-- Evaluation point for the first-derivative rule: `x_μ = (2μ-1)π/(2R)`. -/
noncomputable def psPoint (R μ : ℕ) : ℝ := (2 * (μ : ℝ) - 1) * Real.pi / (2 * R)

/-- Weight for the first-derivative rule: `(-1)^{μ-1} / (4R sin²((2μ-1)π/(4R)))`. -/
noncomputable def psWeight (R μ : ℕ) : ℝ :=
  (-1 : ℝ) ^ (μ - 1) / (4 * R * Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ^ 2)

/-- Evaluation point for the second-derivative rule: `μπ/R`. -/
noncomputable def psPoint2 (R μ : ℕ) : ℝ := (μ : ℝ) * Real.pi / R

/-- Weight for the second-derivative rule: `(-1)^{μ-1} / (2 sin²(μπ/(2R)))`. -/
noncomputable def psWeight2 (R μ : ℕ) : ℝ :=
  (-1 : ℝ) ^ (μ - 1) / (2 * Real.sin ((μ : ℝ) * Real.pi / (2 * R)) ^ 2)

/-! ### Odd-node evaluations of the kernel arguments

`R·x_μ = (2μ-1)π/2 = μπ - π/2`, so the top frequency evaluates to a sign and the
half-angle stays inside `(0, π)` where `sin` does not vanish. -/

/-- `cos(R x_μ) = 0`: the top-frequency cosine vanishes at every odd node. -/
theorem cos_R_mul_psPoint (R μ : ℕ) (hR : 1 ≤ R) :
    Real.cos ((R : ℝ) * psPoint R μ) = 0 := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (R : ℝ) * psPoint R μ = (μ : ℝ) * Real.pi - Real.pi / 2 := by
    unfold psPoint; field_simp
  rw [key, Real.cos_sub]
  simp [Real.sin_nat_mul_pi]

/-- `sin(R x_μ) = (-1)^{μ-1}`: the top-frequency sine at the odd nodes alternates. -/
theorem sin_R_mul_psPoint (R μ : ℕ) (hR : 1 ≤ R) (hμ : 1 ≤ μ) :
    Real.sin ((R : ℝ) * psPoint R μ) = (-1 : ℝ) ^ (μ - 1) := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (R : ℝ) * psPoint R μ = (μ : ℝ) * Real.pi - Real.pi / 2 := by
    unfold psPoint; field_simp
  have hμ' : μ - 1 + 1 = μ := Nat.sub_add_cancel hμ
  have hpow : (-1 : ℝ) ^ μ = -(-1) ^ (μ - 1) := by
    conv_lhs => rw [← hμ', pow_succ]
    ring
  rw [key, Real.sin_sub]
  simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, hpow]

/-- The half-angle at an odd node lies in `(0, π)`, so `sin(x_μ/2) ≠ 0`. -/
theorem sin_half_psPoint_ne (R μ : ℕ) (hR : 1 ≤ R) (hμ : 1 ≤ μ) (hμR : μ ≤ 2 * R) :
    Real.sin (psPoint R μ / 2) ≠ 0 := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hμpos : (1 : ℝ) ≤ (μ : ℝ) := by exact_mod_cast hμ
  have hμRle : (μ : ℝ) ≤ 2 * (R : ℝ) := by exact_mod_cast hμR
  have hπ : 0 < Real.pi := Real.pi_pos
  have hval : psPoint R μ / 2 = (2 * (μ : ℝ) - 1) * Real.pi / (4 * R) := by
    unfold psPoint; field_simp; ring
  have hnum : (0 : ℝ) < 2 * (μ : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < 4 * (R : ℝ) := by linarith
  refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · rw [hval]; exact div_pos (mul_pos hnum hπ) hden
  · rw [hval, div_lt_iff₀ hden]
    have h1 : (2 * (μ : ℝ) - 1) < 4 * R := by linarith
    calc (2 * (μ : ℝ) - 1) * Real.pi < (4 * R) * Real.pi :=
          mul_lt_mul_of_pos_right h1 hπ
      _ = Real.pi * (4 * R) := by ring

/-! ### The modified Dirichlet kernel

The modified Dirichlet kernel is the explicit degree-`R` cosine polynomial
`D̃(x) = 1/(2R) + 1/(2R) cos(R x) + (1/R) ∑_{ℓ=1}^{R-1} cos(ℓ x)`.
Equivalently `2R · sin(x/2) · D̃(x) = sin(R x) cos(x/2)`. The following singularity-
free master identity packages that relation; differentiating it supplies the node
weights without ever dividing by `sin`. -/

/-- **Master identity.** `sin(R x) cos(x/2) = sin(x/2) · (1 + cos(R x) + 2 ∑_{ℓ=1}^{R-1} cos(ℓ x))`.
Proved by induction on `R` with the sum-to-product identities. -/
theorem dirichlet_master (R : ℕ) (hR : 1 ≤ R) (x : ℝ) :
    Real.sin ((R : ℝ) * x) * Real.cos (x / 2)
      = Real.sin (x / 2) * (1 + Real.cos ((R : ℝ) * x)
          + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * x)) := by
  induction R, hR using Nat.le_induction with
  | base =>
    have hcosx : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
      have h := Real.cos_sq (x / 2)
      rw [show 2 * (x / 2) = x from by ring] at h; linarith
    have hsinx : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
      have h := Real.sin_two_mul (x / 2)
      rw [show 2 * (x / 2) = x from by ring] at h; linarith
    simp only [Nat.cast_one, one_mul, Nat.sub_self,
      Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0), Finset.sum_empty, mul_zero, add_zero]
    rw [hsinx, hcosx]; ring
  | succ n hn ih =>
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have key : ∑ ℓ ∈ Finset.Icc 1 n, Real.cos ((ℓ : ℝ) * x)
             = (∑ ℓ ∈ Finset.Icc 1 (n - 1), Real.cos ((ℓ : ℝ) * x)) + Real.cos ((n : ℝ) * x) := by
      conv_lhs => rw [← hn1]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n - 1 + 1), hn1]
    have e1 : Real.sin (((n : ℝ) + 1) * x) - Real.sin ((n : ℝ) * x)
            = 2 * Real.sin (x / 2) * Real.cos ((2 * (n : ℝ) + 1) * x / 2) := by
      rw [Real.sin_sub_sin,
        show (((n : ℝ) + 1) * x - (n : ℝ) * x) / 2 = x / 2 from by ring,
        show (((n : ℝ) + 1) * x + (n : ℝ) * x) / 2 = (2 * (n : ℝ) + 1) * x / 2 from by ring]
    have e2 : Real.cos (((n : ℝ) + 1) * x) + Real.cos ((n : ℝ) * x)
            = 2 * Real.cos ((2 * (n : ℝ) + 1) * x / 2) * Real.cos (x / 2) := by
      rw [Real.cos_add_cos,
        show (((n : ℝ) + 1) * x + (n : ℝ) * x) / 2 = (2 * (n : ℝ) + 1) * x / 2 from by ring,
        show (((n : ℝ) + 1) * x - (n : ℝ) * x) / 2 = x / 2 from by ring]
    simp only [Nat.add_sub_cancel]
    rw [key]
    push_cast
    linear_combination ih + Real.cos (x / 2) * e1 - Real.sin (x / 2) * e2

/-- **First derivative of the master identity** (as a pointwise value equality obtained by
differentiating both sides). The sine sub-sum appears in the raw form
`∑ -sin(ℓ x)·ℓ` coming from term-by-term differentiation. -/
theorem dirichlet_master_deriv (R : ℕ) (hR : 1 ≤ R) (x : ℝ) :
    (R : ℝ) * Real.cos ((R : ℝ) * x) * Real.cos (x / 2)
        - (1 / 2) * Real.sin ((R : ℝ) * x) * Real.sin (x / 2)
      = (1 / 2) * Real.cos (x / 2)
          * (1 + Real.cos ((R : ℝ) * x) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * x))
        + Real.sin (x / 2)
          * (-(Real.sin ((R : ℝ) * x) * (R : ℝ))
              + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) := by
  have hRt : HasDerivAt (fun t : ℝ => (R : ℝ) * t) (R : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (R : ℝ)
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 2
  -- derivative of the master LHS `sin(R·) cos(·/2)`, in raw product-rule form
  have hF := hRt.sin.mul hhalf.cos
  -- derivative of the sub-sum `∑ cos(ℓ·)`, term by term
  have hsum : HasDerivAt (fun t => ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
      (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x := by
    have hterm : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
        HasDerivAt (fun t : ℝ => Real.cos ((ℓ : ℝ) * t)) (-Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x := by
      intro ℓ _
      have hℓ : HasDerivAt (fun t : ℝ => (ℓ : ℝ) * t) (ℓ : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (ℓ : ℝ)
      exact hℓ.cos
    have hs := HasDerivAt.sum hterm
    have key : (∑ ℓ ∈ Finset.Icc 1 (R - 1), fun t : ℝ => Real.cos ((ℓ : ℝ) * t))
             = fun t : ℝ => ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t) := by
      funext t; simp only [Finset.sum_apply]
    rw [key] at hs
    exact hs
  -- derivative of the master RHS `sin(·/2) · (1 + cos(R·) + 2 ∑ cos(ℓ·))`; the explicit
  -- lambda type keeps the factor a genuine function (not a `Pi`-algebra expression) so
  -- that the product-rule derivative beta-reduces cleanly.
  have hP : HasDerivAt
      (fun t => 1 + Real.cos ((R : ℝ) * t) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
      (0 + -Real.sin ((R : ℝ) * x) * (R : ℝ)
        + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x :=
    ((hasDerivAt_const x (1 : ℝ)).add hRt.cos).add (hsum.const_mul 2)
  have hRHS := hhalf.sin.mul hP
  have master : (fun t => Real.sin ((R : ℝ) * t) * Real.cos (t / 2))
              = (fun t => Real.sin (t / 2)
                  * (1 + Real.cos ((R : ℝ) * t)
                      + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))) :=
    funext (fun t => dirichlet_master R hR t)
  -- transport the LHS-derivative fact across the (propositional) master equality
  have hF' : HasDerivAt
      (fun t => Real.sin (t / 2)
        * (1 + Real.cos ((R : ℝ) * t) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t)))
      (Real.cos ((R : ℝ) * x) * (R : ℝ) * Real.cos (x / 2)
        + Real.sin ((R : ℝ) * x) * (-Real.sin (x / 2) * (1 / 2))) x := by
    rw [← master]; exact hF
  have hkey := hF'.unique hRHS
  linear_combination hkey

/-- **Second derivative of the master identity.** This pointwise equality is used only at
the even nodes, where `sin(R x) = 0`; it resolves the second-derivative weights into a
finite cosine polynomial. -/
theorem dirichlet_master_deriv2 (R : ℕ) (hR : 1 ≤ R) (x : ℝ) :
    -((R : ℝ) ^ 2) * Real.sin ((R : ℝ) * x) * Real.cos (x / 2)
        - (R : ℝ) * Real.cos ((R : ℝ) * x) * Real.sin (x / 2)
        - (1 / 4) * Real.sin ((R : ℝ) * x) * Real.cos (x / 2)
      = -(1 / 4) * Real.sin (x / 2)
          * (1 + Real.cos ((R : ℝ) * x) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * x))
        + Real.cos (x / 2)
          * (-(Real.sin ((R : ℝ) * x) * (R : ℝ))
              + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ))
        + Real.sin (x / 2)
          * (-((R : ℝ) ^ 2) * Real.cos ((R : ℝ) * x)
              + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
                -Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2) := by
  have hRt : HasDerivAt (fun t : ℝ => (R : ℝ) * t) (R : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (R : ℝ)
  have hhalf : HasDerivAt (fun t : ℝ => t / 2) (1 / 2 : ℝ) x := by
    simpa using (hasDerivAt_id x).div_const 2
  have hsum1 : HasDerivAt (fun t => ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
      (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x := by
    have hterm : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
        HasDerivAt (fun t : ℝ => Real.cos ((ℓ : ℝ) * t)) (-Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x := by
      intro ℓ _
      have hℓ : HasDerivAt (fun t : ℝ => (ℓ : ℝ) * t) (ℓ : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (ℓ : ℝ)
      exact hℓ.cos
    have hs := HasDerivAt.sum hterm
    have key : (∑ ℓ ∈ Finset.Icc 1 (R - 1), fun t : ℝ => Real.cos ((ℓ : ℝ) * t))
             = fun t : ℝ => ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t) := by
      funext t; simp only [Finset.sum_apply]
    rw [key] at hs
    exact hs
  have hsum2 : HasDerivAt
      (fun t => ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ))
      (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2) x := by
    have hterm : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
        HasDerivAt (fun t : ℝ => -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ))
          (-Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2) x := by
      intro ℓ _
      have hℓ : HasDerivAt (fun t : ℝ => (ℓ : ℝ) * t) (ℓ : ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (ℓ : ℝ)
      have hs := hℓ.sin
      have ht := hs.const_mul (-(ℓ : ℝ))
      have hfun : (fun t : ℝ => -(ℓ : ℝ) * Real.sin ((ℓ : ℝ) * t))
            = fun t : ℝ => -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ) := by
        funext t; ring
      rw [hfun] at ht
      have hder : -(ℓ : ℝ) * (Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ))
          = -Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2 := by ring
      rw [hder] at ht
      exact ht
    have hs := HasDerivAt.sum hterm
    have key : (∑ ℓ ∈ Finset.Icc 1 (R - 1), fun t : ℝ => -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ))
             = fun t : ℝ => ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ) := by
      funext t; simp only [Finset.sum_apply]
    rw [key] at hs
    exact hs
  have hP : HasDerivAt
      (fun t => 1 + Real.cos ((R : ℝ) * t) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
      (0 + -Real.sin ((R : ℝ) * x) * (R : ℝ)
        + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ)) x :=
    ((hasDerivAt_const x (1 : ℝ)).add hRt.cos).add (hsum1.const_mul 2)
  have hQ : HasDerivAt
      (fun t => -(Real.sin ((R : ℝ) * t) * (R : ℝ))
          + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ))
      (-((R : ℝ) ^ 2) * Real.cos ((R : ℝ) * x)
          + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2) x := by
    have htop0 := hRt.sin.const_mul (-(R : ℝ))
    have htop_fun : (fun t : ℝ => -(R : ℝ) * Real.sin ((R : ℝ) * t))
        = fun t : ℝ => -(Real.sin ((R : ℝ) * t) * (R : ℝ)) := by
      funext t; ring
    rw [htop_fun] at htop0
    have htop_der : -(R : ℝ) * (Real.cos ((R : ℝ) * x) * (R : ℝ))
        = -((R : ℝ) ^ 2) * Real.cos ((R : ℝ) * x) := by ring
    rw [htop_der] at htop0
    exact htop0.add (hsum2.const_mul 2)
  have hF₁ :=
    ((hRt.cos.const_mul (R : ℝ)).mul hhalf.cos).sub
      ((hRt.sin.mul hhalf.sin).const_mul (1 / 2))
  have hF₂ := ((hhalf.cos.const_mul (1 / 2)).mul hP).add (hhalf.sin.mul hQ)
  have masterD :
      (fun t : ℝ => (R : ℝ) * Real.cos ((R : ℝ) * t) * Real.cos (t / 2)
          - (1 / 2) * Real.sin ((R : ℝ) * t) * Real.sin (t / 2))
        =
      (fun t : ℝ => (1 / 2) * Real.cos (t / 2)
          * (1 + Real.cos ((R : ℝ) * t) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
        + Real.sin (t / 2)
          * (-(Real.sin ((R : ℝ) * t) * (R : ℝ))
              + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ))) :=
    funext (fun t => dirichlet_master_deriv R hR t)
  have hF₁' : HasDerivAt
      (fun t : ℝ => (1 / 2) * Real.cos (t / 2)
          * (1 + Real.cos ((R : ℝ) * t) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * t))
        + Real.sin (t / 2)
          * (-(Real.sin ((R : ℝ) * t) * (R : ℝ))
              + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * t) * (ℓ : ℝ)))
      ((R : ℝ) * (-Real.sin ((R : ℝ) * x) * (R : ℝ)) * Real.cos (x / 2)
        + (R : ℝ) * Real.cos ((R : ℝ) * x) * (-Real.sin (x / 2) * (1 / 2))
        - (1 / 2) * (Real.cos ((R : ℝ) * x) * (R : ℝ) * Real.sin (x / 2)
          + Real.sin ((R : ℝ) * x) * (Real.cos (x / 2) * (1 / 2)))) x := by
    rw [← masterD]
    have hfun :
        (fun t : ℝ => (R : ℝ) * Real.cos ((R : ℝ) * t) * Real.cos (t / 2)
          - (1 / 2) * Real.sin ((R : ℝ) * t) * Real.sin (t / 2))
          =
        ((((fun y : ℝ => (R : ℝ) * Real.cos ((R : ℝ) * y)) * fun y : ℝ => Real.cos (y / 2))
          - fun y : ℝ => (1 / 2) * ((fun y : ℝ => Real.sin ((R : ℝ) * y))
            * fun y : ℝ => Real.sin (y / 2)) y)) := by
      funext t
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    rw [hfun]
    exact hF₁
  have hkey := hF₁'.unique hF₂
  linear_combination hkey

/-- **Odd-node weight resolution.** Where `cos(R x) = 0` (an odd node) and `sin(x/2) ≠ 0`,
the singular weight `sin(R x)/(4R sin²(x/2))` equals a trigonometric polynomial of degree `R`.
This is the identity that removes the `1/sin²` from the parameter-shift weights. -/
theorem weight_odd_resolve (R : ℕ) (hR : 1 ≤ R) (x : ℝ)
    (hcos : Real.cos ((R : ℝ) * x) = 0) (hsin : Real.sin (x / 2) ≠ 0) :
    Real.sin ((R : ℝ) * x) / (4 * (R : ℝ) * Real.sin (x / 2) ^ 2)
      = (1 / 2) * Real.sin ((R : ℝ) * x)
        - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ) := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpyth : Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x / 2)
  have hM := dirichlet_master R hR x
  have hD := dirichlet_master_deriv R hR x
  rw [hcos] at hM hD
  -- eliminate the `1/sin²` and the shared cosine sum, leaving a clean quadratic relation
  have hstar : Real.sin (x / 2) ^ 2
        * (Real.sin ((R : ℝ) * x) * (R : ℝ)
            - 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ))
      = (1 / 2) * Real.sin ((R : ℝ) * x) := by
    linear_combination Real.sin (x / 2) * hD - (Real.cos (x / 2) / 2) * hM
      + (Real.sin ((R : ℝ) * x) / 2) * hpyth
  have hne : 4 * (R : ℝ) * Real.sin (x / 2) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hR0) (pow_ne_zero 2 hsin)
  rw [div_eq_iff hne]
  have hclear : ((1 / 2) * Real.sin ((R : ℝ) * x)
        - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ))
        * (4 * (R : ℝ) * Real.sin (x / 2) ^ 2)
      = 2 * (Real.sin (x / 2) ^ 2
          * (Real.sin ((R : ℝ) * x) * (R : ℝ)
              - 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * x) * (ℓ : ℝ))) := by
    field_simp
    ring
  rw [hclear, hstar]
  ring

/-- **Even-node weight resolution.** Where `sin(R x) = 0` and `sin(x/2) ≠ 0`,
the second-derivative singular weight is a finite cosine polynomial. -/
theorem weight_even_resolve (R : ℕ) (hR : 1 ≤ R) (x : ℝ)
    (hsinR : Real.sin ((R : ℝ) * x) = 0) (hsin : Real.sin (x / 2) ≠ 0) :
    -Real.cos ((R : ℝ) * x) / (2 * Real.sin (x / 2) ^ 2)
      = -((R : ℝ) / 2) * Real.cos ((R : ℝ) * x)
        - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * x) := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs2 : Real.sin (x / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
  have hpyth : Real.sin (x / 2) ^ 2 + Real.cos (x / 2) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (x / 2)
  have hM := dirichlet_master R hR x
  rw [hsinR] at hM
  have hP0 :
      1 + Real.cos ((R : ℝ) * x) + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * x) = 0 := by
    have hzero : Real.sin (x / 2)
        * (1 + Real.cos ((R : ℝ) * x)
          + 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1), Real.cos ((ℓ : ℝ) * x)) = 0 := by
      simpa using hM.symm
    exact (mul_eq_zero.mp hzero).resolve_left hsin
  have hD := dirichlet_master_deriv R hR x
  have hD2 := dirichlet_master_deriv2 R hR x
  rw [hsinR, hP0] at hD hD2
  rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.cos ((ℓ : ℝ) * x) * (ℓ : ℝ) ^ 2)
      = -∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ)) by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun ℓ _ => by
        ring_nf] at hD2
  ring_nf at hD hD2
  have hpyth' : Real.sin (x * (1 / 2)) ^ 2 + Real.cos (x * (1 / 2)) ^ 2 = 1 := by
    convert hpyth using 1
    ring_nf
  have hD' :
      (R : ℝ) * Real.cos (x * (R : ℝ)) * Real.cos (x * (1 / 2))
        = 2 * (Real.sin (x * (1 / 2))
          * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin (x * (ℓ : ℝ)))) := by
    simpa [show (R : ℝ) * x = x * (R : ℝ) by ring, mul_comm, mul_left_comm, mul_assoc]
      using hD
  have hD2' :
      -((R : ℝ) * Real.cos (x * (R : ℝ)) * Real.sin (x * (1 / 2)))
        = -((R : ℝ) ^ 2 * Real.cos (x * (R : ℝ)) * Real.sin (x * (1 / 2)))
          + 2 * (Real.cos (x * (1 / 2))
            * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin (x * (ℓ : ℝ))))
          - 2 * (Real.sin (x * (1 / 2))
            * ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ))) := by
    simpa [show (R : ℝ) * x = x * (R : ℝ) by ring, mul_comm, mul_left_comm, mul_assoc,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hD2
  have hstar : Real.sin (x * (1 / 2)) ^ 2
        * (-((R : ℝ) ^ 2) * Real.cos (x * (R : ℝ))
          - 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ)))
      = -(R : ℝ) * Real.cos (x * (R : ℝ)) := by
    have hcomb :
        -((R : ℝ) * Real.cos (x * (R : ℝ)))
            * (Real.sin (x * (1 / 2)) ^ 2 + Real.cos (x * (1 / 2)) ^ 2)
          =
        Real.sin (x * (1 / 2)) ^ 2
          * (-((R : ℝ) ^ 2) * Real.cos (x * (R : ℝ))
            - 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ))) := by
      calc
        -((R : ℝ) * Real.cos (x * (R : ℝ)))
            * (Real.sin (x * (1 / 2)) ^ 2 + Real.cos (x * (1 / 2)) ^ 2)
            =
          Real.sin (x * (1 / 2))
              * (-((R : ℝ) * Real.cos (x * (R : ℝ)) * Real.sin (x * (1 / 2))))
            - Real.cos (x * (1 / 2))
              * ((R : ℝ) * Real.cos (x * (R : ℝ)) * Real.cos (x * (1 / 2))) := by
          ring
        _ =
          Real.sin (x * (1 / 2))
              * (-((R : ℝ) ^ 2 * Real.cos (x * (R : ℝ)) * Real.sin (x * (1 / 2)))
                + 2 * (Real.cos (x * (1 / 2))
                  * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin (x * (ℓ : ℝ))))
                - 2 * (Real.sin (x * (1 / 2))
                  * ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ))))
            - Real.cos (x * (1 / 2))
              * (2 * (Real.sin (x * (1 / 2))
                * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin (x * (ℓ : ℝ))))) := by
          rw [hD2', hD']
        _ = Real.sin (x * (1 / 2)) ^ 2
          * (-((R : ℝ) ^ 2) * Real.cos (x * (R : ℝ))
            - 2 * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ))) := by
          ring
    rw [← hcomb, hpyth']
    ring
  rw [show x / 2 = x * (1 / 2) by ring]
  rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * x))
      = ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 * Real.cos (x * (ℓ : ℝ)) by
      exact Finset.sum_congr rfl fun ℓ _ => by
        congr 1
        ring_nf]
  rw [show (R : ℝ) * x = x * (R : ℝ) by ring]
  have hs2' : Real.sin (x * (1 / 2)) ^ 2 ≠ 0 := by
    simpa [show x / 2 = x * (1 / 2) by ring] using hs2
  field_simp [hR0, hs2']
  rw [show Real.sin (x / 2) ^ 2 = Real.sin (x * (1 / 2)) ^ 2 by
    congr 1
    ring_nf]
  convert hstar.symm using 1 <;> ring_nf

/-! ### Discrete orthogonality on the odd nodes

Two telescoping identities give the finite trigonometric sums over the `2R` odd nodes
`(2μ-1)π/(2R)` without any complex-exponential machinery. -/

/-- Telescoping cosine sum: `2 sinθ · ∑_{μ=1}^{n} cos((2μ-1)θ) = sin(2nθ)`. -/
theorem sin_mul_sum_cos_odd (θ : ℝ) (n : ℕ) :
    2 * Real.sin θ * ∑ μ ∈ Finset.Icc 1 n, Real.cos ((2 * (μ : ℝ) - 1) * θ)
      = Real.sin (2 * (n : ℝ) * θ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have hps : Real.sin (2 * ((k : ℝ) + 1) * θ) - Real.sin (2 * (k : ℝ) * θ)
             = 2 * Real.sin θ * Real.cos ((2 * ((k : ℝ) + 1) - 1) * θ) := by
      rw [Real.sin_sub_sin,
        show (2 * ((k : ℝ) + 1) * θ - 2 * (k : ℝ) * θ) / 2 = θ from by ring,
        show (2 * ((k : ℝ) + 1) * θ + 2 * (k : ℝ) * θ) / 2 =
          (2 * ((k : ℝ) + 1) - 1) * θ from by ring]
    push_cast
    linear_combination -hps

/-- Telescoping sine sum: `2 sinθ · ∑_{μ=1}^{n} sin((2μ-1)θ) = 1 - cos(2nθ)`. -/
theorem sin_mul_sum_sin_odd (θ : ℝ) (n : ℕ) :
    2 * Real.sin θ * ∑ μ ∈ Finset.Icc 1 n, Real.sin ((2 * (μ : ℝ) - 1) * θ)
      = 1 - Real.cos (2 * (n : ℝ) * θ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have hps : Real.cos (2 * (k : ℝ) * θ) - Real.cos (2 * ((k : ℝ) + 1) * θ)
             = 2 * Real.sin θ * Real.sin ((2 * ((k : ℝ) + 1) - 1) * θ) := by
      rw [Real.cos_sub_cos,
        show (2 * (k : ℝ) * θ + 2 * ((k : ℝ) + 1) * θ) / 2 =
          (2 * ((k : ℝ) + 1) - 1) * θ from by ring,
        show (2 * (k : ℝ) * θ - 2 * ((k : ℝ) + 1) * θ) / 2 = -θ from by ring, Real.sin_neg]
      ring
    push_cast
    linear_combination -hps

/-- Telescoping cosine sum on the ordinary grid:
`2 sin(θ/2) · ∑_{μ=1}^{n} cos(μθ) = sin(nθ + θ/2) - sin(θ/2)`. -/
theorem sin_half_mul_sum_cos_even (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ μ ∈ Finset.Icc 1 n, Real.cos ((μ : ℝ) * θ)
      = Real.sin ((n : ℝ) * θ + θ / 2) - Real.sin (θ / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have hps : Real.sin (((k : ℝ) + 1) * θ + θ / 2) - Real.sin ((k : ℝ) * θ + θ / 2)
             = 2 * Real.sin (θ / 2) * Real.cos (((k : ℝ) + 1) * θ) := by
      rw [Real.sin_sub_sin,
        show ((((k : ℝ) + 1) * θ + θ / 2) - ((k : ℝ) * θ + θ / 2)) / 2 = θ / 2 from by ring,
        show ((((k : ℝ) + 1) * θ + θ / 2) + ((k : ℝ) * θ + θ / 2)) / 2 =
          ((k : ℝ) + 1) * θ from by ring]
    push_cast
    linear_combination -hps

/-- Telescoping sine sum on the ordinary grid:
`2 sin(θ/2) · ∑_{μ=1}^{n} sin(μθ) = cos(θ/2) - cos(nθ + θ/2)`. -/
theorem sin_half_mul_sum_sin_even (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ μ ∈ Finset.Icc 1 n, Real.sin ((μ : ℝ) * θ)
      = Real.cos (θ / 2) - Real.cos ((n : ℝ) * θ + θ / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have hps : Real.cos ((k : ℝ) * θ + θ / 2) - Real.cos (((k : ℝ) + 1) * θ + θ / 2)
             = 2 * Real.sin (θ / 2) * Real.sin (((k : ℝ) + 1) * θ) := by
      rw [Real.cos_sub_cos,
        show (((k : ℝ) * θ + θ / 2) + (((k : ℝ) + 1) * θ + θ / 2)) / 2 =
          ((k : ℝ) + 1) * θ from by ring,
        show (((k : ℝ) * θ + θ / 2) - (((k : ℝ) + 1) * θ + θ / 2)) / 2 = -θ / 2 from by ring,
        show -θ / 2 = -(θ / 2) from by ring,
        Real.sin_neg]
      ring
    push_cast
    linear_combination -hps

/-- A node multiple rewritten into telescoping form: `m · x_μ = (2μ-1)·(mπ/2R)`. -/
theorem mul_psPoint (R m μ : ℕ) :
    (m : ℝ) * psPoint R μ = (2 * (μ : ℝ) - 1) * ((m : ℝ) * Real.pi / (2 * R)) := by
  unfold psPoint; ring

/-- A node multiple rewritten into ordinary-grid form: `m · y_μ = μ·(mπ/R)`. -/
theorem mul_psPoint2 (R m μ : ℕ) :
    (m : ℝ) * psPoint2 R μ = (μ : ℝ) * ((m : ℝ) * Real.pi / R) := by
  unfold psPoint2; ring

private theorem sin_mul_cos_eq (x y : ℝ) :
    Real.sin x * Real.cos y = (Real.sin (x + y) + Real.sin (x - y)) / 2 := by
  rw [Real.sin_add, Real.sin_sub]
  ring

private theorem sin_mul_sin_eq (x y : ℝ) :
    Real.sin x * Real.sin y = (Real.cos (x - y) - Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private theorem cos_mul_cos_eq (x y : ℝ) :
    Real.cos x * Real.cos y = (Real.cos (x + y) + Real.cos (x - y)) / 2 := by
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Every sine sum over the `2R` odd nodes vanishes. -/
theorem sum_sin_psPoint (R m : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), Real.sin ((m : ℝ) * psPoint R μ) = 0 := by
  simp only [mul_psPoint]
  set θ := (m : ℝ) * Real.pi / (2 * R) with hθdef
  by_cases hs : Real.sin θ = 0
  · apply Finset.sum_eq_zero
    intro μ _
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    rw [← hn, show (2 * (μ : ℝ) - 1) * ((n : ℝ) * Real.pi)
        = (((2 * (μ : ℤ) - 1) * n : ℤ) : ℝ) * Real.pi from by push_cast; ring]
    exact Real.sin_int_mul_pi _
  · have htel := sin_mul_sum_sin_odd θ (2 * R)
    have h2 : Real.cos (2 * ((2 * R : ℕ) : ℝ) * θ) = 1 := by
      have hR0 : (2 * (R : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
        positivity
      rw [hθdef, show 2 * ((2 * R : ℕ) : ℝ) * ((m : ℝ) * Real.pi / (2 * R))
          = ((m : ℤ) : ℝ) * (2 * Real.pi) from by push_cast; field_simp]
      exact Real.cos_int_mul_two_pi m
    rw [h2, sub_self] at htel
    rcases mul_eq_zero.mp htel with h | h
    · exact absurd (by linarith : Real.sin θ = 0) hs
    · exact h

/-- Interior cosine sums over the odd nodes vanish (`1 ≤ m ≤ 2R-1`). -/
theorem sum_cos_psPoint_of_lt (R m : ℕ) (hR : 1 ≤ R) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * R - 1) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), Real.cos ((m : ℝ) * psPoint R μ) = 0 := by
  simp only [mul_psPoint]
  set θ := (m : ℝ) * Real.pi / (2 * R) with hθdef
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmlt : (m : ℝ) < 2 * (R : ℝ) := by
    have : m < 2 * R := by omega
    exact_mod_cast this
  have hsθ : Real.sin θ ≠ 0 := by
    rw [hθdef]
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · exact div_pos (mul_pos hmpos Real.pi_pos) (by linarith)
    · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (R : ℝ))]
      calc (m : ℝ) * Real.pi < (2 * (R : ℝ)) * Real.pi :=
            mul_lt_mul_of_pos_right hmlt Real.pi_pos
        _ = Real.pi * (2 * (R : ℝ)) := by ring
  have htel := sin_mul_sum_cos_odd θ (2 * R)
  have h0 : Real.sin (2 * ((2 * R : ℕ) : ℝ) * θ) = 0 := by
    rw [hθdef, show 2 * ((2 * R : ℕ) : ℝ) * ((m : ℝ) * Real.pi / (2 * R))
        = ((2 * m : ℕ) : ℝ) * Real.pi from by push_cast; field_simp]
    exact Real.sin_nat_mul_pi _
  rw [h0] at htel
  rcases mul_eq_zero.mp htel with h | h
  · exact absurd (by linarith : Real.sin θ = 0) hsθ
  · exact h

/-- The zero-frequency cosine sum counts the nodes: `∑ cos(0·x_μ) = 2R`. -/
theorem sum_cos_psPoint_zero (R : ℕ) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), Real.cos ((0 : ℝ) * psPoint R μ) = 2 * (R : ℝ) := by
  simp only [zero_mul, Real.cos_zero, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_one]
  push_cast; ring

/-- The top even-multiple cosine sum: `∑ cos(2R·x_μ) = -2R` (each `cos((2μ-1)π) = -1`). -/
theorem sum_cos_psPoint_2R (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ) = -(2 * (R : ℝ)) := by
  have hR0 : (R : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    exact ne_of_gt this
  have hterm : ∀ μ ∈ Finset.Icc 1 (2 * R),
      Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ) = -1 := by
    intro μ hμ
    have hμ1 : 1 ≤ μ := (Finset.mem_Icc.mp hμ).1
    have hcast : ((2 * μ - 1 : ℕ) : ℝ) = 2 * (μ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * μ)]; push_cast; ring
    have harg : ((2 * R : ℕ) : ℝ) * psPoint R μ = ((2 * μ - 1 : ℕ) : ℝ) * Real.pi := by
      rw [hcast]; unfold psPoint; push_cast; field_simp
    rw [harg, Real.cos_nat_mul_pi]
    exact Odd.neg_one_pow ⟨μ - 1, by omega⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul, mul_neg, mul_one]
  push_cast; ring

/-! ### Discrete sums on the even nodes -/

/-- Every sine sum over the `2R - 1` nonzero even nodes vanishes. -/
theorem sum_sin_psPoint2 (R m : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.sin ((m : ℝ) * psPoint2 R μ) = 0 := by
  simp only [mul_psPoint2]
  set θ := (m : ℝ) * Real.pi / R with hθdef
  by_cases hs : Real.sin (θ / 2) = 0
  · apply Finset.sum_eq_zero
    intro μ _
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hs
    have hθ : θ = 2 * (n : ℝ) * Real.pi := by linarith
    rw [hθ, show (μ : ℝ) * (2 * (n : ℝ) * Real.pi)
        = (((2 * μ : ℕ) : ℤ) * n : ℤ) * Real.pi by push_cast; ring]
    exact Real.sin_int_mul_pi _
  · have htel := sin_half_mul_sum_sin_even θ (2 * R - 1)
    have hend : Real.cos (((2 * R - 1 : ℕ) : ℝ) * θ + θ / 2) = Real.cos (θ / 2) := by
      rw [hθdef]
      have hR0 : (R : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
        exact ne_of_gt this
      have hcast : ((2 * R - 1 : ℕ) : ℝ) = 2 * (R : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * R)]
        push_cast
        ring
      rw [hcast]
      have hangle : (2 * (R : ℝ) - 1) * ((m : ℝ) * Real.pi / R)
              + ((m : ℝ) * Real.pi / R) / 2
          = ((2 * m : ℕ) : ℝ) * Real.pi - ((m : ℝ) * Real.pi / R) / 2 := by
        push_cast
        field_simp [hR0]
        ring_nf
      rw [hangle, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
      rw [Even.neg_one_pow ⟨m, by omega⟩]
      ring
    rw [hend, sub_self] at htel
    rcases mul_eq_zero.mp htel with h | h
    · exact absurd (by linarith : Real.sin (θ / 2) = 0) hs
    · exact h

/-- The zero-frequency cosine sum over the even nodes counts `2R - 1` samples. -/
theorem sum_cos_psPoint2_zero (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.cos ((0 : ℝ) * psPoint2 R μ)
      = 2 * (R : ℝ) - 1 := by
  simp only [zero_mul, Real.cos_zero, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have hcard : 2 * R - 1 + 1 - 1 = 2 * R - 1 := by omega
  rw [hcard]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * R)]
  push_cast
  ring_nf

/-- Interior cosine sums over the even nodes equal `-1` (`1 ≤ m ≤ 2R - 1`). -/
theorem sum_cos_psPoint2_of_lt (R m : ℕ) (hR : 1 ≤ R) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * R - 1) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.cos ((m : ℝ) * psPoint2 R μ) = -1 := by
  simp only [mul_psPoint2]
  set θ := (m : ℝ) * Real.pi / R with hθdef
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmlt : (m : ℝ) < 2 * (R : ℝ) := by
    have : m < 2 * R := by omega
    exact_mod_cast this
  have hsθ : Real.sin (θ / 2) ≠ 0 := by
    rw [hθdef, show ((m : ℝ) * Real.pi / R) / 2 = (m : ℝ) * Real.pi / (2 * R) by
      field_simp [hR0]]
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · exact div_pos (mul_pos hmpos Real.pi_pos) (by linarith)
    · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (R : ℝ))]
      calc (m : ℝ) * Real.pi < (2 * (R : ℝ)) * Real.pi :=
            mul_lt_mul_of_pos_right hmlt Real.pi_pos
        _ = Real.pi * (2 * (R : ℝ)) := by ring
  have htel := sin_half_mul_sum_cos_even θ (2 * R - 1)
  have hend : Real.sin (((2 * R - 1 : ℕ) : ℝ) * θ + θ / 2) = -Real.sin (θ / 2) := by
    rw [hθdef]
    have hcast : ((2 * R - 1 : ℕ) : ℝ) = 2 * (R : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * R)]
      push_cast
      ring
    rw [hcast]
    have hangle : (2 * (R : ℝ) - 1) * ((m : ℝ) * Real.pi / R)
            + ((m : ℝ) * Real.pi / R) / 2
        = ((2 * m : ℕ) : ℝ) * Real.pi - ((m : ℝ) * Real.pi / R) / 2 := by
      push_cast
      field_simp [hR0]
      ring_nf
    rw [hangle, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    rw [Even.neg_one_pow ⟨m, by omega⟩]
    ring
  rw [hend] at htel
  have hclear : 2 * Real.sin (θ / 2) * ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.cos ((μ : ℝ) * θ)
      = -2 * Real.sin (θ / 2) := by linarith
  have hne : 2 * Real.sin (θ / 2) ≠ 0 := mul_ne_zero (by norm_num) hsθ
  have hclear' :
      (2 * Real.sin (θ / 2)) * ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.cos ((μ : ℝ) * θ)
        = (2 * Real.sin (θ / 2)) * (-1) := by
    rw [hclear]
    ring
  exact mul_left_cancel₀ hne hclear'

/-- The full-period cosine sum over the even nodes counts all samples. -/
theorem sum_cos_psPoint2_2R (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ)
      = 2 * (R : ℝ) - 1 := by
  have hR0 : (R : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
    exact ne_of_gt this
  have hterm : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ) = 1 := by
    intro μ _
    have harg : ((2 * R : ℕ) : ℝ) * psPoint2 R μ = ((2 * μ : ℕ) : ℝ) * Real.pi := by
      unfold psPoint2
      push_cast
      field_simp [hR0]
    rw [harg, Real.cos_nat_mul_pi]
    exact Even.neg_one_pow ⟨μ, by omega⟩
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have hcard : 2 * R - 1 + 1 - 1 = 2 * R - 1 := by omega
  rw [hcard]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * R)]
  push_cast
  ring_nf

/-- Every integer-frequency sine sum over the nonzero even nodes vanishes. -/
theorem sum_sin_int_mul_psPoint2 (R : ℕ) (m : ℤ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.sin ((m : ℝ) * psPoint2 R μ) = 0 := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa using sum_sin_psPoint2 R n hR
  · simp_rw [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg]
    calc
      ∑ μ ∈ Finset.Icc 1 (2 * R - 1), -Real.sin ((n : ℝ) * psPoint2 R μ)
          = -∑ μ ∈ Finset.Icc 1 (2 * R - 1), Real.sin ((n : ℝ) * psPoint2 R μ) := by
            rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [sum_sin_psPoint2 R n hR, neg_zero]

/-- Even-node mixed sine/cosine orthogonality. -/
theorem sum_sin_mul_cos_psPoint2_eq_zero (R p q : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.sin ((p : ℝ) * psPoint2 R μ) * Real.cos ((q : ℝ) * psPoint2 R μ) = 0 := by
  have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.sin ((p : ℝ) * psPoint2 R μ) * Real.cos ((q : ℝ) * psPoint2 R μ)
        =
          (Real.sin (((p + q : ℕ) : ℝ) * psPoint2 R μ)
            + Real.sin ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * psPoint2 R μ)) / 2 := by
    intro μ _
    have hplus : Real.sin ((p : ℝ) * psPoint2 R μ + (q : ℝ) * psPoint2 R μ)
        = Real.sin (((p + q : ℕ) : ℝ) * psPoint2 R μ) := by
      congr 1
      push_cast
      ring
    have hminus : Real.sin ((p : ℝ) * psPoint2 R μ - (q : ℝ) * psPoint2 R μ)
        = Real.sin ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * psPoint2 R μ) := by
      congr 1
      push_cast
      ring
    rw [sin_mul_cos_eq, hplus, hminus]
  rw [Finset.sum_congr rfl hprod]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        (Real.sin (((p + q : ℕ) : ℝ) * psPoint2 R μ)
          + Real.sin ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * psPoint2 R μ)) / 2)
      =
        (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.sin (((p + q : ℕ) : ℝ) * psPoint2 R μ)
          + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.sin ((((p : ℤ) - (q : ℤ) : ℤ) : ℝ) * psPoint2 R μ)) / 2 by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
  rw [sum_sin_psPoint2 R (p + q) hR, sum_sin_int_mul_psPoint2 R ((p : ℤ) - (q : ℤ)) hR]
  ring

/-- Even-node cosine/cosine products below the top second factor. -/
theorem sum_cos_mul_cos_psPoint2_of_lt (R p q : ℕ) (hR : 1 ≤ R)
    (hp1 : 1 ≤ p) (hpR : p ≤ R) (hq1 : 1 ≤ q) (hqR : q ≤ R - 1) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((q : ℝ) * psPoint2 R μ)
        = if p = q then (R : ℝ) - 1 else -1 := by
  by_cases hpq : p = q
  · subst q
    simp only [if_true]
    have hp_lt : p ≤ R - 1 := hqR
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((p : ℝ) * psPoint2 R μ)
          = (1 + Real.cos (((2 * p : ℕ) : ℝ) * psPoint2 R μ)) / 2 := by
      intro μ _
      have harg : Real.cos (((p : ℝ) * psPoint2 R μ) + (p : ℝ) * psPoint2 R μ)
            + Real.cos (((p : ℝ) * psPoint2 R μ) - (p : ℝ) * psPoint2 R μ)
          = Real.cos (((2 * p : ℕ) : ℝ) * psPoint2 R μ) + 1 := by
        push_cast
        rw [sub_self, Real.cos_zero]
        congr 1
        ring_nf
      rw [mul_comm, cos_mul_cos_eq]
      rw [show (Real.cos (((p : ℝ) * psPoint2 R μ) + (p : ℝ) * psPoint2 R μ)
            + Real.cos (((p : ℝ) * psPoint2 R μ) - (p : ℝ) * psPoint2 R μ))
          = Real.cos (((2 * p : ℕ) : ℝ) * psPoint2 R μ) + 1 from harg]
      ring
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (1 + Real.cos (((2 * p : ℕ) : ℝ) * psPoint2 R μ)) / 2)
        =
          ((∑ μ ∈ Finset.Icc 1 (2 * R - 1), (1 : ℝ))
            + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.cos (((2 * p : ℕ) : ℝ) * psPoint2 R μ)) / 2 by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint2_of_lt R (2 * p) hR (by omega) (by omega)]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have hcard : 2 * R - 1 + 1 - 1 = 2 * R - 1 := by omega
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ 2 * R)]
    push_cast
    ring
  · rw [if_neg hpq]
    by_cases hpq_lt : p < q
    · have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((q : ℝ) * psPoint2 R μ)
            =
              (Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
                + Real.cos (((q - p : ℕ) : ℝ) * psPoint2 R μ)) / 2 := by
        intro μ _
        rw [mul_comm, cos_mul_cos_eq]
        congr 2
        · congr 1
          push_cast
          ring
        · congr 1
          rw [Nat.cast_sub (by omega : p ≤ q)]
          ring
      rw [Finset.sum_congr rfl hprod]
      rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            (Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
              + Real.cos (((q - p : ℕ) : ℝ) * psPoint2 R μ)) / 2)
          =
            (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
              + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos (((q - p : ℕ) : ℝ) * psPoint2 R μ)) / 2 by
          rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
      rw [sum_cos_psPoint2_of_lt R (p + q) hR (by omega) (by omega),
        sum_cos_psPoint2_of_lt R (q - p) hR (by omega) (by omega)]
      ring
    · have hqp_lt : q < p := by omega
      have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((q : ℝ) * psPoint2 R μ)
            =
              (Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
                + Real.cos (((p - q : ℕ) : ℝ) * psPoint2 R μ)) / 2 := by
        intro μ _
        rw [cos_mul_cos_eq]
        congr 2
        · congr 1
          push_cast
          ring
        · congr 1
          rw [Nat.cast_sub (by omega : q ≤ p)]
          ring
      rw [Finset.sum_congr rfl hprod]
      rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            (Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
              + Real.cos (((p - q : ℕ) : ℝ) * psPoint2 R μ)) / 2)
          =
            (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos (((p + q : ℕ) : ℝ) * psPoint2 R μ)
              + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos (((p - q : ℕ) : ℝ) * psPoint2 R μ)) / 2 by
          rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
      rw [sum_cos_psPoint2_of_lt R (p + q) hR (by omega) (by omega),
        sum_cos_psPoint2_of_lt R (p - q) hR (by omega) (by omega)]
      ring

/-- Even-node cosine/top-frequency cosine products. -/
theorem sum_cos_mul_cos_top_psPoint2 (R p : ℕ) (hR : 1 ≤ R) (hp1 : 1 ≤ p) (hpR : p ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ)
        = if p = R then 2 * (R : ℝ) - 1 else -1 := by
  by_cases hp : p = R
  · subst p
    simp only [if_true]
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.cos ((R : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ)
          = (1 + Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ)) / 2 := by
      intro μ _
      have harg : Real.cos (((R : ℝ) * psPoint2 R μ) + (R : ℝ) * psPoint2 R μ)
            + Real.cos (((R : ℝ) * psPoint2 R μ) - (R : ℝ) * psPoint2 R μ)
          = Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ) + 1 := by
        push_cast
        rw [sub_self, Real.cos_zero]
        congr 1
        ring_nf
      rw [mul_comm, cos_mul_cos_eq]
      rw [show (Real.cos (((R : ℝ) * psPoint2 R μ) + (R : ℝ) * psPoint2 R μ)
            + Real.cos (((R : ℝ) * psPoint2 R μ) - (R : ℝ) * psPoint2 R μ))
          = Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ) + 1 from harg]
      ring
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (1 + Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ)) / 2)
        =
          ((∑ μ ∈ Finset.Icc 1 (2 * R - 1), (1 : ℝ))
            + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.cos (((2 * R : ℕ) : ℝ) * psPoint2 R μ)) / 2 by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint2_2R R hR]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have hcard : 2 * R - 1 + 1 - 1 = 2 * R - 1 := by omega
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ 2 * R)]
    push_cast
    ring
  · rw [if_neg hp]
    have hp_lt : p ≤ R - 1 := by omega
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ)
          =
            (Real.cos (((p + R : ℕ) : ℝ) * psPoint2 R μ)
              + Real.cos (((R - p : ℕ) : ℝ) * psPoint2 R μ)) / 2 := by
      intro μ _
      rw [mul_comm, cos_mul_cos_eq]
      congr 2
      · congr 1
        push_cast
        ring
      · congr 1
        rw [Nat.cast_sub (by omega : p ≤ R)]
        ring
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (Real.cos (((p + R : ℕ) : ℝ) * psPoint2 R μ)
            + Real.cos (((R - p : ℕ) : ℝ) * psPoint2 R μ)) / 2)
        =
          (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.cos (((p + R : ℕ) : ℝ) * psPoint2 R μ)
            + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.cos (((R - p : ℕ) : ℝ) * psPoint2 R μ)) / 2 by
        rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint2_of_lt R (p + R) hR (by omega) (by omega),
      sum_cos_psPoint2_of_lt R (R - p) hR (by omega) (by omega)]
    ring

/-! ### Per-frequency parameter-shift identities (second derivative) -/

/-- `sin(R y_μ) = 0` on the even nodes. -/
theorem sin_R_mul_psPoint2 (R μ : ℕ) (hR : 1 ≤ R) :
    Real.sin ((R : ℝ) * psPoint2 R μ) = 0 := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (R : ℝ) * psPoint2 R μ = (μ : ℝ) * Real.pi := by
    unfold psPoint2
    field_simp [hR0]
  rw [key]
  exact Real.sin_nat_mul_pi μ

/-- `cos(R y_μ) = (-1)^μ` on the even nodes. -/
theorem cos_R_mul_psPoint2 (R μ : ℕ) (hR : 1 ≤ R) :
    Real.cos ((R : ℝ) * psPoint2 R μ) = (-1 : ℝ) ^ μ := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have key : (R : ℝ) * psPoint2 R μ = (μ : ℝ) * Real.pi := by
    unfold psPoint2
    field_simp [hR0]
  rw [key, Real.cos_nat_mul_pi]

/-- The half-angle at a nonzero even node lies in `(0, π)`, so its sine is nonzero. -/
theorem sin_half_psPoint2_ne (R μ : ℕ) (hR : 1 ≤ R) (hμ : 1 ≤ μ) (hμR : μ ≤ 2 * R - 1) :
    Real.sin (psPoint2 R μ / 2) ≠ 0 := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR0 : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  have hμpos : (0 : ℝ) < (μ : ℝ) := by exact_mod_cast hμ
  have hμlt : (μ : ℝ) < 2 * (R : ℝ) := by
    have : μ < 2 * R := by omega
    exact_mod_cast this
  have hval : psPoint2 R μ / 2 = (μ : ℝ) * Real.pi / (2 * R) := by
    unfold psPoint2
    field_simp [hR0]
  refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
  · rw [hval]
    exact div_pos (mul_pos hμpos Real.pi_pos) (by linarith)
  · rw [hval, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (R : ℝ))]
    calc (μ : ℝ) * Real.pi < (2 * (R : ℝ)) * Real.pi :=
          mul_lt_mul_of_pos_right hμlt Real.pi_pos
      _ = Real.pi * (2 * (R : ℝ)) := by ring

/-- The second-derivative weight rewritten with `-cos(R y_μ)` in the numerator. -/
theorem psWeight2_eq (R μ : ℕ) (hR : 1 ≤ R) (hμ : 1 ≤ μ) :
    psWeight2 R μ
      = -Real.cos ((R : ℝ) * psPoint2 R μ) / (2 * Real.sin (psPoint2 R μ / 2) ^ 2) := by
  have hhalf : psPoint2 R μ / 2 = (μ : ℝ) * Real.pi / (2 * R) := by
    unfold psPoint2
    ring
  have hsign : (-1 : ℝ) ^ (μ - 1) = -Real.cos ((R : ℝ) * psPoint2 R μ) := by
    rw [cos_R_mul_psPoint2 R μ hR]
    have hμ' : μ - 1 + 1 = μ := Nat.sub_add_cancel hμ
    have hpow : (-1 : ℝ) ^ μ = -(-1 : ℝ) ^ (μ - 1) := by
      conv_lhs => rw [← hμ', pow_succ]
      ring
    rw [hpow]
    ring
  unfold psWeight2
  rw [hhalf, hsign]

/-- **(E0)** The second-derivative weights sum to the constant-cancellation coefficient. -/
theorem sum_psWeight2_eq (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1), psWeight2 R μ
      = (2 * (R : ℝ) ^ 2 + 1) / 6 := by
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
      psWeight2 R μ
        = -((R : ℝ) / 2) * Real.cos ((R : ℝ) * psPoint2 R μ)
          - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight2_eq R μ hR hμ1]
    exact weight_even_resolve R hR (psPoint2 R μ) (sin_R_mul_psPoint2 R μ hR)
      (sin_half_psPoint2_ne R μ hR hμ1 hμ2)
  have hinner : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
      ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ) = -((ℓ : ℝ) ^ 2) := by
    intro ℓ hℓ
    obtain ⟨hℓ1, hℓR⟩ := Finset.mem_Icc.mp hℓ
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))
        = (ℓ : ℝ) ^ 2 * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((ℓ : ℝ) * psPoint2 R μ) by
        rw [Finset.mul_sum]]
    rw [sum_cos_psPoint2_of_lt R ℓ hR hℓ1 (by omega)]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_cos_psPoint2_of_lt R R hR hR (by omega)]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        1 / (R : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))
      =
        1 / (R : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ) by
      calc
        (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          1 / (R : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))
            =
          1 / (R : ℝ) * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ) := by
          rw [Finset.mul_sum]
        _ = 1 / (R : ℝ) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              (ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ) := by
          rw [Finset.sum_comm]]
  rw [Finset.sum_congr rfl hinner]
  rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) ^ 2))
      = -∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 by
      rw [Finset.sum_neg_distrib]]
  rw [sum_sq_Icc_one_sub R]
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hR0]
  ring

/-- **(E1)** The second-derivative weights annihilate every sine coefficient. -/
theorem sum_sin_mul_psWeight2_eq_zero (R p : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.sin ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ = 0 := by
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.sin ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ
        = -((R : ℝ) / 2)
            * (Real.sin ((p : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ))
          - Real.sin ((p : ℝ) * psPoint2 R μ)
              * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
                (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight2_eq R μ hR hμ1]
    rw [weight_even_resolve R hR (psPoint2 R μ) (sin_R_mul_psPoint2 R μ hR)
      (sin_half_psPoint2_ne R μ hR hμ1 hμ2)]
    rw [Finset.mul_sum]
    ring
  have hinner : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
      ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.sin ((p : ℝ) * psPoint2 R μ)
          * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) = 0 := by
    intro ℓ _
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.sin ((p : ℝ) * psPoint2 R μ)
            * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))))
        = ((ℓ : ℝ) ^ 2 * (1 / (R : ℝ))) * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.sin ((p : ℝ) * psPoint2 R μ) * Real.cos ((ℓ : ℝ) * psPoint2 R μ) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring]
    rw [sum_sin_mul_cos_psPoint2_eq_zero R p ℓ hR, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_sin_mul_cos_psPoint2_eq_zero R p R hR, mul_zero, zero_sub]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.sin ((p : ℝ) * psPoint2 R μ)
          * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
      =
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.sin ((p : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) by
      calc
        (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.sin ((p : ℝ) * psPoint2 R μ)
            * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
            =
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              Real.sin ((p : ℝ) * psPoint2 R μ)
                * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) := by
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.mul_sum]
        _ = ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.sin ((p : ℝ) * psPoint2 R μ)
                * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) := by
          rw [Finset.sum_comm]]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const_zero]
  ring

/-- **(E2)** The second-derivative weights extract the cosine coefficient
`(2R² + 1)/6 - p²`. -/
theorem sum_cos_mul_psWeight2_eq (R p : ℕ) (hR : 1 ≤ R) (hp1 : 1 ≤ p) (hpR : p ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.cos ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ
        = (2 * (R : ℝ) ^ 2 + 1) / 6 - (p : ℝ) ^ 2 := by
  have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
      Real.cos ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ
        = -((R : ℝ) / 2)
            * (Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ))
          - Real.cos ((p : ℝ) * psPoint2 R μ)
              * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
                (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight2_eq R μ hR hμ1]
    rw [weight_even_resolve R hR (psPoint2 R μ) (sin_R_mul_psPoint2 R μ hR)
      (sin_half_psPoint2_ne R μ hR hμ1 hμ2)]
    rw [Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_cos_mul_cos_top_psPoint2 R p hR hp1 hpR]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
        Real.cos ((p : ℝ) * psPoint2 R μ)
          * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
      =
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((p : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) by
      calc
        (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          Real.cos ((p : ℝ) * psPoint2 R μ)
            * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
            =
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              Real.cos ((p : ℝ) * psPoint2 R μ)
                * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) := by
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.mul_sum]
        _ = ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              Real.cos ((p : ℝ) * psPoint2 R μ)
                * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))) := by
          rw [Finset.sum_comm]]
  by_cases hp : p = R
  · subst p
    have hinner :
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((R : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
          = -(1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 := by
      rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((R : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))))
          = ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((1 / (R : ℝ)) * (ℓ : ℝ) ^ 2) by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          obtain ⟨hℓ1, hℓR⟩ := Finset.mem_Icc.mp hℓ
          rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos ((R : ℝ) * psPoint2 R μ)
                  * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))))
              = (1 / (R : ℝ)) * (ℓ : ℝ) ^ 2
                  * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                    Real.cos ((ℓ : ℝ) * psPoint2 R μ) * Real.cos ((R : ℝ) * psPoint2 R μ) by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun μ _ => by ring]
          rw [sum_cos_mul_cos_top_psPoint2 R ℓ hR hℓ1 (by omega)]
          rw [if_neg (by omega : ¬ℓ = R)]
          ring]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    rw [if_pos rfl, hinner, sum_sq_Icc_one_sub R]
    field_simp [hR0]
    ring
  · have hp_lt : p ≤ R - 1 := by omega
    have hp_mem : p ∈ Finset.Icc 1 (R - 1) := Finset.mem_Icc.mpr ⟨hp1, hp_lt⟩
    have hinner :
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((p : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ)))
          = (p : ℝ) ^ 2 - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 := by
      calc
        (∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            Real.cos ((p : ℝ) * psPoint2 R μ)
              * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))))
            =
          ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            (1 / (R : ℝ)) * (ℓ : ℝ) ^ 2
              * (if p = ℓ then ((R : ℝ) - 1) else (-1 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          obtain ⟨hℓ1, hℓR⟩ := Finset.mem_Icc.mp hℓ
          rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos ((p : ℝ) * psPoint2 R μ)
                  * ((1 / (R : ℝ)) * ((ℓ : ℝ) ^ 2 * Real.cos ((ℓ : ℝ) * psPoint2 R μ))))
              = (1 / (R : ℝ)) * (ℓ : ℝ) ^ 2
                  * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                    Real.cos ((p : ℝ) * psPoint2 R μ) * Real.cos ((ℓ : ℝ) * psPoint2 R μ) by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun μ _ => by ring]
          rw [sum_cos_mul_cos_psPoint2_of_lt R p ℓ hR hp1 hpR hℓ1 hℓR]
        _ = ∑ ℓ ∈ Finset.Icc 1 (R - 1),
              (-((1 / (R : ℝ)) * (ℓ : ℝ) ^ 2)
                + if ℓ = p then (1 / (R : ℝ)) * (ℓ : ℝ) ^ 2 * (R : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro ℓ _
          by_cases hℓp : ℓ = p
          · subst ℓ
            rw [if_pos rfl, if_pos rfl]
            ring
          · rw [if_neg (by intro h; exact hℓp h.symm), if_neg hℓp]
            ring
        _ = -(1 / (R : ℝ)) * (∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2)
              + (1 / (R : ℝ)) * (p : ℝ) ^ 2 * (R : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
          have hcorr :
              (∑ ℓ ∈ Finset.Icc 1 (R - 1),
                if ℓ = p then (1 / (R : ℝ)) * (ℓ : ℝ) ^ 2 * (R : ℝ) else 0)
                = (1 / (R : ℝ)) * (p : ℝ) ^ 2 * (R : ℝ) := by
            rw [Finset.sum_eq_single p]
            · rw [if_pos rfl]
            · intro ℓ hℓ hℓp
              rw [if_neg hℓp]
            · intro hp_not_mem
              exact False.elim (hp_not_mem hp_mem)
          rw [hcorr]
          ring
        _ = (p : ℝ) ^ 2 - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1), (ℓ : ℝ) ^ 2 := by
          field_simp [hR0]
          ring
    rw [if_neg hp, hinner, sum_sq_Icc_one_sub R]
    field_simp [hR0]
    ring

/-! ### Per-frequency parameter-shift identities (first derivative) -/

/-- The parameter-shift weight rewritten with `sin(R x_μ)` in the numerator. -/
theorem psWeight_eq (R μ : ℕ) (hR : 1 ≤ R) (hμ : 1 ≤ μ) :
    psWeight R μ
      = Real.sin ((R : ℝ) * psPoint R μ) / (4 * (R : ℝ) * Real.sin (psPoint R μ / 2) ^ 2) := by
  have h2 : psPoint R μ / 2 = (2 * (μ : ℝ) - 1) * Real.pi / (4 * R) := by unfold psPoint; ring
  unfold psWeight
  rw [sin_R_mul_psPoint R μ hR hμ, h2]

/-- **(C0)** The weights sum to zero, so a constant loss contributes nothing to the rule. -/
theorem sum_psWeight_eq_zero (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), psWeight R μ = 0 := by
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R), psWeight R μ
      = (1 / 2) * Real.sin ((R : ℝ) * psPoint R μ)
        - (1 / (R : ℝ)) * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          -Real.sin ((ℓ : ℝ) * psPoint R μ) * (ℓ : ℝ) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight_eq R μ hR hμ1]
    exact weight_odd_resolve R hR (psPoint R μ) (cos_R_mul_psPoint R μ hR)
      (sin_half_psPoint_ne R μ hR hμ1 hμ2)
  have hinner : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
      ∑ μ ∈ Finset.Icc 1 (2 * R), -Real.sin ((ℓ : ℝ) * psPoint R μ) * (ℓ : ℝ) = 0 := by
    intro ℓ _
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R), -Real.sin ((ℓ : ℝ) * psPoint R μ) * (ℓ : ℝ))
        = -(ℓ : ℝ) * ∑ μ ∈ Finset.Icc 1 (2 * R), Real.sin ((ℓ : ℝ) * psPoint R μ) from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring]
    rw [sum_sin_psPoint R ℓ hR, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_sin_psPoint R R hR, Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const_zero]
  ring

/-- Every integer-frequency sine sum over the `2R` odd nodes vanishes. -/
theorem sum_sin_int_mul_psPoint (R : ℕ) (m : ℤ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), Real.sin ((m : ℝ) * psPoint R μ) = 0 := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · simpa using sum_sin_psPoint R n hR
  · simp_rw [Int.cast_neg, Int.cast_natCast, neg_mul, Real.sin_neg]
    calc
      ∑ μ ∈ Finset.Icc 1 (2 * R), -Real.sin ((n : ℝ) * psPoint R μ)
          = -∑ μ ∈ Finset.Icc 1 (2 * R), Real.sin ((n : ℝ) * psPoint R μ) := by
            rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [sum_sin_psPoint R n hR, neg_zero]

/-- Odd-node mixed cosine/sine orthogonality. -/
theorem sum_cos_mul_sin_psPoint_eq_zero (R m n : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R),
      Real.cos ((m : ℝ) * psPoint R μ) * Real.sin ((n : ℝ) * psPoint R μ) = 0 := by
  have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
      Real.cos ((m : ℝ) * psPoint R μ) * Real.sin ((n : ℝ) * psPoint R μ)
        =
          (Real.sin (((n + m : ℕ) : ℝ) * psPoint R μ)
            + Real.sin ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * psPoint R μ)) / 2 := by
    intro μ _
    have hplus : Real.sin ((n : ℝ) * psPoint R μ + (m : ℝ) * psPoint R μ)
        = Real.sin (((n + m : ℕ) : ℝ) * psPoint R μ) := by
      congr 1
      push_cast
      ring
    have hminus : Real.sin ((n : ℝ) * psPoint R μ - (m : ℝ) * psPoint R μ)
        = Real.sin ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * psPoint R μ) := by
      congr 1
      push_cast
      ring
    rw [mul_comm, sin_mul_cos_eq]
    rw [hplus, hminus]
  rw [Finset.sum_congr rfl hprod]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
        (Real.sin (((n + m : ℕ) : ℝ) * psPoint R μ)
          + Real.sin ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * psPoint R μ)) / 2)
      =
        (∑ μ ∈ Finset.Icc 1 (2 * R),
          Real.sin (((n + m : ℕ) : ℝ) * psPoint R μ)
          + ∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * psPoint R μ)) / 2 by
      rw [← Finset.sum_add_distrib, ← Finset.sum_div]]
  rw [sum_sin_psPoint R (n + m) hR, sum_sin_int_mul_psPoint R ((n : ℤ) - (m : ℤ)) hR]
  ring

/-- Odd-node sine/sine orthogonality below the top frequency. -/
theorem sum_sin_mul_sin_psPoint_of_lt (R m n : ℕ) (hR : 1 ≤ R)
    (hm1 : 1 ≤ m) (hmR : m ≤ R - 1) (hn1 : 1 ≤ n) (hnR : n ≤ R - 1) :
    ∑ μ ∈ Finset.Icc 1 (2 * R),
      Real.sin ((m : ℝ) * psPoint R μ) * Real.sin ((n : ℝ) * psPoint R μ)
        = if m = n then (R : ℝ) else 0 := by
  by_cases hmn : m = n
  · subst n
    simp only [if_true]
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
        Real.sin ((m : ℝ) * psPoint R μ) * Real.sin ((m : ℝ) * psPoint R μ)
          = (1 - Real.cos (((2 * m : ℕ) : ℝ) * psPoint R μ)) / 2 := by
      intro μ _
      have harg : Real.cos (((m : ℝ) * psPoint R μ) - (m : ℝ) * psPoint R μ)
            - Real.cos (((m : ℝ) * psPoint R μ) + (m : ℝ) * psPoint R μ)
          = 1 - Real.cos (((2 * m : ℕ) : ℝ) * psPoint R μ) := by
        push_cast
        rw [sub_self, Real.cos_zero]
        congr 1
        ring_nf
      rw [sin_mul_sin_eq, harg]
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
          (1 - Real.cos (((2 * m : ℕ) : ℝ) * psPoint R μ)) / 2)
        =
          ((∑ μ ∈ Finset.Icc 1 (2 * R), (1 : ℝ))
            - ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos (((2 * m : ℕ) : ℝ) * psPoint R μ)) / 2 by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint_of_lt R (2 * m) hR (by omega) (by omega)]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one,
      sub_zero]
    push_cast
    ring
  · rw [if_neg hmn]
    by_cases hmn_lt : m < n
    · have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
          Real.sin ((m : ℝ) * psPoint R μ) * Real.sin ((n : ℝ) * psPoint R μ)
            =
              (Real.cos (((n - m : ℕ) : ℝ) * psPoint R μ)
                - Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2 := by
        intro μ _
        rw [mul_comm, sin_mul_sin_eq]
        congr 2
        · congr 1
          rw [Nat.cast_sub (by omega : m ≤ n)]
          ring
        · congr 1
          push_cast
          ring
      rw [Finset.sum_congr rfl hprod]
      rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
            (Real.cos (((n - m : ℕ) : ℝ) * psPoint R μ)
              - Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2)
          =
            (∑ μ ∈ Finset.Icc 1 (2 * R),
                Real.cos (((n - m : ℕ) : ℝ) * psPoint R μ)
              - ∑ μ ∈ Finset.Icc 1 (2 * R),
                Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2 by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_div]]
      rw [sum_cos_psPoint_of_lt R (n - m) hR (by omega) (by omega),
        sum_cos_psPoint_of_lt R (m + n) hR (by omega) (by omega)]
      ring
    · have hmn_gt : n < m := by omega
      have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
          Real.sin ((m : ℝ) * psPoint R μ) * Real.sin ((n : ℝ) * psPoint R μ)
            =
              (Real.cos (((m - n : ℕ) : ℝ) * psPoint R μ)
                - Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2 := by
        intro μ _
        rw [sin_mul_sin_eq]
        congr 2
        · congr 1
          rw [Nat.cast_sub (by omega : n ≤ m)]
          ring
        · congr 1
          push_cast
          ring
      rw [Finset.sum_congr rfl hprod]
      rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
            (Real.cos (((m - n : ℕ) : ℝ) * psPoint R μ)
              - Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2)
          =
            (∑ μ ∈ Finset.Icc 1 (2 * R),
                Real.cos (((m - n : ℕ) : ℝ) * psPoint R μ)
              - ∑ μ ∈ Finset.Icc 1 (2 * R),
                Real.cos (((m + n : ℕ) : ℝ) * psPoint R μ)) / 2 by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_div]]
      rw [sum_cos_psPoint_of_lt R (m - n) hR (by omega) (by omega),
        sum_cos_psPoint_of_lt R (m + n) hR (by omega) (by omega)]
      ring

/-- Odd-node sine/top-frequency sine orthogonality. -/
theorem sum_sin_mul_sin_top_psPoint (R p : ℕ) (hR : 1 ≤ R) (hp1 : 1 ≤ p) (hpR : p ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R),
      Real.sin ((p : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ)
        = if p = R then 2 * (R : ℝ) else 0 := by
  by_cases hp : p = R
  · subst p
    simp only [if_true]
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
        Real.sin ((R : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ)
          = (1 - Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ)) / 2 := by
      intro μ _
      have harg : Real.cos (((R : ℝ) * psPoint R μ) - (R : ℝ) * psPoint R μ)
            - Real.cos (((R : ℝ) * psPoint R μ) + (R : ℝ) * psPoint R μ)
          = 1 - Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ) := by
        push_cast
        rw [sub_self, Real.cos_zero]
        congr 1
        ring_nf
      rw [sin_mul_sin_eq, harg]
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
          (1 - Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ)) / 2)
        =
          ((∑ μ ∈ Finset.Icc 1 (2 * R), (1 : ℝ))
            - ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos (((2 * R : ℕ) : ℝ) * psPoint R μ)) / 2 by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint_2R R hR]
    simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · rw [if_neg hp]
    have hp_lt : p ≤ R - 1 := by omega
    have hprod : ∀ μ ∈ Finset.Icc 1 (2 * R),
        Real.sin ((p : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ)
          =
            (Real.cos (((R - p : ℕ) : ℝ) * psPoint R μ)
              - Real.cos (((p + R : ℕ) : ℝ) * psPoint R μ)) / 2 := by
      intro μ _
      rw [mul_comm, sin_mul_sin_eq]
      congr 2
      · congr 1
        rw [Nat.cast_sub (by omega : p ≤ R)]
        ring
      · congr 1
        push_cast
        ring
    rw [Finset.sum_congr rfl hprod]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
          (Real.cos (((R - p : ℕ) : ℝ) * psPoint R μ)
            - Real.cos (((p + R : ℕ) : ℝ) * psPoint R μ)) / 2)
        =
          (∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos (((R - p : ℕ) : ℝ) * psPoint R μ)
            - ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos (((p + R : ℕ) : ℝ) * psPoint R μ)) / 2 by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_div]]
    rw [sum_cos_psPoint_of_lt R (R - p) hR (by omega) (by omega),
      sum_cos_psPoint_of_lt R (p + R) hR (by omega) (by omega)]
    ring

/-- **(C1)** Odd-node weights annihilate every cosine coefficient. -/
theorem sum_cos_mul_psWeight_eq_zero (R p : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R),
      Real.cos ((p : ℝ) * psPoint R μ) * psWeight R μ = 0 := by
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R),
      Real.cos ((p : ℝ) * psPoint R μ) * psWeight R μ
        = (1 / 2) * (Real.cos ((p : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ))
          - Real.cos ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
                -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight_eq R μ hR hμ1]
    rw [weight_odd_resolve R hR (psPoint R μ) (cos_R_mul_psPoint R μ hR)
      (sin_half_psPoint_ne R μ hR hμ1 hμ2)]
    rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * psPoint R μ) * (ℓ : ℝ))
        = ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)) by
        exact Finset.sum_congr rfl fun ℓ _ => by ring]
    ring
  have hinner : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
      ∑ μ ∈ Finset.Icc 1 (2 * R),
        Real.cos ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
          * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))) = 0 := by
    intro ℓ _
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
          Real.cos ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
            * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))))
        = -((ℓ : ℝ) * (1 / (R : ℝ))) * ∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.cos ((p : ℝ) * psPoint R μ) * Real.sin ((ℓ : ℝ) * psPoint R μ) by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => by ring]
    rw [sum_cos_mul_sin_psPoint_eq_zero R p ℓ hR, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_cos_mul_sin_psPoint_eq_zero R p R hR, mul_zero, zero_sub]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
        Real.cos ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
          * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)))
      =
        ∑ μ ∈ Finset.Icc 1 (2 * R),
          ∑ ℓ ∈ Finset.Icc 1 (R - 1),
            Real.cos ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))) by
      apply Finset.sum_congr rfl
      intro μ _
      rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const_zero]
  ring

/-- **(S1)** Odd-node weights extract the sine coefficient `p`. -/
theorem sum_sin_mul_psWeight_eq (R p : ℕ) (hR : 1 ≤ R) (hp1 : 1 ≤ p) (hpR : p ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R),
      Real.sin ((p : ℝ) * psPoint R μ) * psWeight R μ = (p : ℝ) := by
  have hstep : ∀ μ ∈ Finset.Icc 1 (2 * R),
      Real.sin ((p : ℝ) * psPoint R μ) * psWeight R μ
        = (1 / 2) * (Real.sin ((p : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ))
          - Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * ∑ ℓ ∈ Finset.Icc 1 (R - 1),
                -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)) := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_Icc.mp hμ
    rw [psWeight_eq R μ hR hμ1]
    rw [weight_odd_resolve R hR (psPoint R μ) (cos_R_mul_psPoint R μ hR)
      (sin_half_psPoint_ne R μ hR hμ1 hμ2)]
    rw [show (∑ ℓ ∈ Finset.Icc 1 (R - 1), -Real.sin ((ℓ : ℝ) * psPoint R μ) * (ℓ : ℝ))
        = ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)) by
        exact Finset.sum_congr rfl fun ℓ _ => by ring]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_sin_mul_sin_top_psPoint R p hR hp1 hpR]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
        Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
          * ∑ ℓ ∈ Finset.Icc 1 (R - 1), -((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ)))
      =
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))) by
      rw [← Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro μ _
      rw [Finset.mul_sum]]
  by_cases hp : p = R
  · subst p
    have hinner : ∀ ℓ ∈ Finset.Icc 1 (R - 1),
        ∑ μ ∈ Finset.Icc 1 (2 * R),
          Real.sin ((R : ℝ) * psPoint R μ) * (1 / (R : ℝ))
            * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))) = 0 := by
      intro ℓ hℓ
      obtain ⟨hℓ1, hℓR⟩ := Finset.mem_Icc.mp hℓ
      rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
          Real.sin ((R : ℝ) * psPoint R μ) * (1 / (R : ℝ))
            * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))))
        = -((ℓ : ℝ) * (1 / (R : ℝ))) * ∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((ℓ : ℝ) * psPoint R μ) * Real.sin ((R : ℝ) * psPoint R μ) by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun μ _ => by ring]
      rw [sum_sin_mul_sin_top_psPoint R ℓ hR hℓ1 (by omega)]
      rw [if_neg (by omega : ¬ℓ = R)]
      ring
    rw [if_pos rfl, Finset.sum_congr rfl hinner, Finset.sum_const_zero]
    ring
  · have hp_lt : p ≤ R - 1 := by omega
    have hR0 : (R : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hp_mem : p ∈ Finset.Icc 1 (R - 1) := Finset.mem_Icc.mpr ⟨hp1, hp_lt⟩
    have hinner :
        ∑ ℓ ∈ Finset.Icc 1 (R - 1),
          ∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))) = -(p : ℝ) := by
      rw [Finset.sum_eq_single p]
      · rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * (-((p : ℝ) * Real.sin ((p : ℝ) * psPoint R μ))))
          = -((p : ℝ) * (1 / (R : ℝ))) * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.sin ((p : ℝ) * psPoint R μ) * Real.sin ((p : ℝ) * psPoint R μ) by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun μ _ => by ring]
        rw [sum_sin_mul_sin_psPoint_of_lt R p p hR hp1 hp_lt hp1 hp_lt, if_pos rfl]
        field_simp [hR0]
      · intro ℓ hℓ hℓp
        obtain ⟨hℓ1, hℓR⟩ := Finset.mem_Icc.mp hℓ
        rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
            Real.sin ((p : ℝ) * psPoint R μ) * (1 / (R : ℝ))
              * (-((ℓ : ℝ) * Real.sin ((ℓ : ℝ) * psPoint R μ))))
          = -((ℓ : ℝ) * (1 / (R : ℝ))) * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.sin ((p : ℝ) * psPoint R μ) * Real.sin ((ℓ : ℝ) * psPoint R μ) by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun μ _ => by ring]
        rw [sum_sin_mul_sin_psPoint_of_lt R p ℓ hR hp1 hp_lt hℓ1 hℓR]
        rw [if_neg (by intro h; exact hℓp h.symm)]
        ring
      · intro hp_not_mem
        exact False.elim (hp_not_mem hp_mem)
    rw [if_neg hp, hinner]
    ring

end QuantumAlg
