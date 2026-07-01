/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

/-!
# The generalized parameter-shift rule

Wierichs, Izaac, Wang, Lin (2022), *General parameter-shift rules for quantum gradients*
(arXiv:2107.12390), Sec. 3.4. For a single-parameter variational loss

`ℓ(x) = a₀ + ∑_{p=1}^R (a_p cos(p x) + b_p sin(p x))`

(a trigonometric polynomial with `R` distinct equidistant integer frequencies — the Fourier
form of `⟨ψ|U†(x) O U(x)|ψ⟩` for `U(x)=e^{ixG}`, Sec. 2.1), the exact first and second
derivatives at the origin are linear combinations of finitely many shifted evaluations.

## What is genuinely proved vs. assumed

* **Proved (this file):** the *derivative side* of the rule — by term-by-term differentiation,
  `ℓ'(0) = ∑_p p·b_p` (`genTrigCost_deriv_zero`) and `ℓ''(0) = -∑_p p²·a_p`
  (`genTrigCost_deriv2_zero`, which reuses the first via the derivative-function identity
  `deriv_genTrigCost`).
* **Assumed (named `structure` fields, cited):** the deep finite trigonometric-sum (Dirichlet
  kernel) identities (`dirichlet_first`, `dirichlet_second`) stating that the specific weighted
  evaluations reproduce `∑_p p·b_p` resp. `-∑_p p²·a_p`. These are the Wierichs App. derivations
  via the (modified) Dirichlet kernel — a genuine analytic identity for every `R`, recorded as a
  named hypothesis (Mathlib has no Dirichlet-kernel theory), **never an `axiom`**.

The closed-form rules `GeneralizedParamShift.firstDeriv` / `secondDeriv` then follow by combining
the proved derivative values with the named Dirichlet identities. The R=1 case recovers the
two-term parameter-shift rule (`QuantumAlg.ParameterShiftRule.main`).

Future work: the Dirichlet-kernel trigonometric-sum identities (`dirichlet_first`,
`dirichlet_second`) are to be proved from scratch as reusable, quantum-free lemmas under
`QuantumAlg/Util/` (e.g. `Util/DirichletKernel.lean`); discharging them there would upgrade this
file to an assumption-free proof of the generalized parameter-shift rule.
-/

@[expose] public section

namespace QuantumAlg

open scoped BigOperators

noncomputable section

/-- The single-parameter variational loss as a degree-`R` trigonometric polynomial
`a₀ + ∑_{p=1}^R (a_p cos(p x) + b_p sin(p x))`. -/
def genTrigCost (a b : ℕ → ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  a 0 + ∑ p ∈ Finset.Icc 1 R, (a p * Real.cos (p * x) + b p * Real.sin (p * x))

/-- The cost is differentiable with the expected term-by-term derivative everywhere. -/
theorem hasDerivAt_genTrigCost (a b : ℕ → ℝ) (R : ℕ) (x : ℝ) :
    HasDerivAt (genTrigCost a b R)
      (∑ p ∈ Finset.Icc 1 R,
        (b p * (p : ℝ) * Real.cos ((p : ℝ) * x) - a p * (p : ℝ) * Real.sin ((p : ℝ) * x))) x := by
  have hterm : ∀ p ∈ Finset.Icc 1 R,
      HasDerivAt (fun y : ℝ => a p * Real.cos ((p : ℝ) * y) + b p * Real.sin ((p : ℝ) * y))
        (b p * (p : ℝ) * Real.cos ((p : ℝ) * x) - a p * (p : ℝ) * Real.sin ((p : ℝ) * x)) x := by
    intro p _
    have hpx : HasDerivAt (fun y : ℝ => (p : ℝ) * y) (p : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (p : ℝ)
    have hc :
        HasDerivAt (fun y : ℝ => Real.cos ((p : ℝ) * y))
          (-Real.sin ((p : ℝ) * x) * (p : ℝ)) x :=
      (Real.hasDerivAt_cos ((p : ℝ) * x)).comp x hpx
    have hs :
        HasDerivAt (fun y : ℝ => Real.sin ((p : ℝ) * y))
          (Real.cos ((p : ℝ) * x) * (p : ℝ)) x :=
      (Real.hasDerivAt_sin ((p : ℝ) * x)).comp x hpx
    have hh := (hc.const_mul (a p)).add (hs.const_mul (b p))
    have heq :
        a p * (-Real.sin ((p : ℝ) * x) * (p : ℝ)) +
            b p * (Real.cos ((p : ℝ) * x) * (p : ℝ))
          =
        b p * (p : ℝ) * Real.cos ((p : ℝ) * x) -
          a p * (p : ℝ) * Real.sin ((p : ℝ) * x) := by
      ring
    rw [heq] at hh
    exact hh
  unfold genTrigCost
  apply HasDerivAt.const_add
  have hsum := HasDerivAt.sum hterm
  have key : (∑ p ∈ Finset.Icc 1 R, fun y : ℝ =>
                a p * Real.cos ((p : ℝ) * y) + b p * Real.sin ((p : ℝ) * y))
           = fun y : ℝ => ∑ p ∈ Finset.Icc 1 R,
                (a p * Real.cos ((p : ℝ) * y) + b p * Real.sin ((p : ℝ) * y)) := by
    funext y
    simp only [Finset.sum_apply]
  rw [key] at hsum
  exact hsum

/-- **First derivative (genuine).** `ℓ'(0) = ∑_{p=1}^R p·b_p`. -/
theorem genTrigCost_deriv_zero (a b : ℕ → ℝ) (R : ℕ) :
    deriv (genTrigCost a b R) 0 = ∑ p ∈ Finset.Icc 1 R, (p : ℝ) * b p := by
  rw [(hasDerivAt_genTrigCost a b R 0).deriv]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, sub_zero]
  ring

/-- The derivative of the cost is again a trigonometric polynomial of the same form. -/
theorem deriv_genTrigCost (a b : ℕ → ℝ) (R : ℕ) :
    deriv (genTrigCost a b R)
      = genTrigCost (fun p => b p * (p : ℝ)) (fun p => -(a p) * (p : ℝ)) R := by
  funext x
  rw [(hasDerivAt_genTrigCost a b R x).deriv]
  unfold genTrigCost
  simp only [Nat.cast_zero, mul_zero, zero_add]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **Second derivative (genuine).** `ℓ''(0) = -∑_{p=1}^R p²·a_p`, reusing the first-derivative
result on the derivative trigonometric polynomial. -/
theorem genTrigCost_deriv2_zero (a b : ℕ → ℝ) (R : ℕ) :
    deriv (deriv (genTrigCost a b R)) 0 = -∑ p ∈ Finset.Icc 1 R, (p : ℝ) ^ 2 * a p := by
  rw [deriv_genTrigCost, genTrigCost_deriv_zero, eq_neg_iff_add_eq_zero,
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun p _ => by ring

/-! ### The generalized parameter-shift rule -/

/-- Evaluation point for the first-derivative rule: `x_μ = (2μ-1)π/(2R)`. -/
def psPoint (R μ : ℕ) : ℝ := (2 * (μ : ℝ) - 1) * Real.pi / (2 * R)

/-- Weight for the first-derivative rule: `(-1)^{μ-1} / (4R sin²((2μ-1)π/(4R)))`. -/
def psWeight (R μ : ℕ) : ℝ :=
  (-1 : ℝ) ^ (μ - 1) / (4 * R * Real.sin ((2 * (μ : ℝ) - 1) * Real.pi / (4 * R)) ^ 2)

/-- Evaluation point for the second-derivative rule: `μπ/R`. -/
def psPoint2 (R μ : ℕ) : ℝ := (μ : ℝ) * Real.pi / R

/-- Weight for the second-derivative rule: `(-1)^{μ-1} / (2 sin²(μπ/(2R)))`. -/
def psWeight2 (R μ : ℕ) : ℝ :=
  (-1 : ℝ) ^ (μ - 1) / (2 * Real.sin ((μ : ℝ) * Real.pi / (2 * R)) ^ 2)

/-- **Generalized parameter-shift data** (Wierichs et al. 2022, Sec. 3.4). The trigonometric-
polynomial coefficients together with the two named Dirichlet-kernel identities (App. derivation)
that the weighted evaluations reproduce the derivatives. The deep finite trigonometric-sum
identities are isolated as hypotheses (no Mathlib Dirichlet-kernel theory); everything else is
derived. -/
structure GeneralizedParamShift (R : ℕ) where
  /-- Cosine coefficients (`a 0` is the constant term). -/
  a : ℕ → ℝ
  /-- Sine coefficients. -/
  b : ℕ → ℝ
  /-- At least one frequency. -/
  hR : 1 ≤ R
  /-- **Dirichlet identity, odd kernels** (Wierichs App.): the `2R`-point weighted evaluation
  reproduces `∑_p p·b_p = ℓ'(0)`. -/
  dirichlet_first :
    ∑ μ ∈ Finset.Icc 1 (2 * R), genTrigCost a b R (psPoint R μ) * psWeight R μ
      = ∑ p ∈ Finset.Icc 1 R, (p : ℝ) * b p
  /-- **Dirichlet identity, even kernels** (Wierichs App.): the weighted evaluation reproduces
  `-∑_p p²·a_p = ℓ''(0)`. -/
  dirichlet_second :
    -genTrigCost a b R 0 * (2 * (R : ℝ) ^ 2 + 1) / 6
        + ∑ μ ∈ Finset.Icc 1 (2 * R - 1), genTrigCost a b R (psPoint2 R μ) * psWeight2 R μ
      = -∑ p ∈ Finset.Icc 1 R, (p : ℝ) ^ 2 * a p

namespace GeneralizedParamShift

variable {R : ℕ} (G : GeneralizedParamShift R)

/-- **Generalized parameter-shift rule (first derivative).** The exact gradient `ℓ'(0)` equals
the `2R`-point weighted sum of shifted evaluations. Combines the genuine derivative
`genTrigCost_deriv_zero` with the named Dirichlet identity. -/
theorem firstDeriv :
    deriv (genTrigCost G.a G.b R) 0
      = ∑ μ ∈ Finset.Icc 1 (2 * R), genTrigCost G.a G.b R (psPoint R μ) * psWeight R μ := by
  rw [genTrigCost_deriv_zero, ← G.dirichlet_first]

/-- **Generalized parameter-shift rule (second derivative).** The exact curvature `ℓ''(0)`
equals the weighted sum of shifted evaluations. -/
theorem secondDeriv :
    deriv (deriv (genTrigCost G.a G.b R)) 0
      = -genTrigCost G.a G.b R 0 * (2 * (R : ℝ) ^ 2 + 1) / 6
        + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            genTrigCost G.a G.b R (psPoint2 R μ) * psWeight2 R μ := by
  rw [genTrigCost_deriv2_zero, ← G.dirichlet_second]

end GeneralizedParamShift

/-- **Non-vacuity.** The hypothesis bundle is satisfiable: the zero cost (`a = b = 0`) on `R = 1`
satisfies both Dirichlet identities (both sides vanish), so the rules are not vacuously true. -/
theorem generalizedParamShift_nonempty : Nonempty (GeneralizedParamShift 1) :=
  ⟨{ a := fun _ => 0
     b := fun _ => 0
     hR := le_refl 1
     dirichlet_first := by simp [genTrigCost]
     dirichlet_second := by simp [genTrigCost] }⟩

end

end QuantumAlg
