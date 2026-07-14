/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.DirichletKernel
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

## What is proved here

* **Proved (this file):** the *derivative side* of the rule — by term-by-term differentiation,
  `ℓ'(0) = ∑_p p·b_p` (`genTrigCost_deriv_zero`) and `ℓ''(0) = -∑_p p²·a_p`
  (`genTrigCost_deriv2_zero`, which reuses the first via the derivative-function identity
  `deriv_genTrigCost`).
* **Proved in `QuantumAlg.Util.DirichletKernel`, assembled here:** the finite trigonometric-sum
  identities (`dirichlet_first_identity`, `dirichlet_second_identity`) stating that the specific
  weighted evaluations reproduce `∑_p p·b_p` resp. `-∑_p p²·a_p`.

The closed-form rules `GeneralizedParamShift.firstDeriv` / `secondDeriv` then follow by combining
the proved derivative values with the proved Dirichlet identities. This is an assumption-free proof
at the abstract `genTrigCost` level; the quantum circuit-to-trigonometric-polynomial bridge remains
a separate follow-up target. The R=1 case recovers the two-term parameter-shift rule
(`QuantumAlg.ParameterShiftRule.main`).
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

/-! ### The generalized parameter-shift rule

The evaluation nodes `psPoint`/`psPoint2` and weights `psWeight`/`psWeight2` are the
quantum-free node data developed in `QuantumAlg.Util.DirichletKernel`. -/

/-- The odd-node Dirichlet identity used by the first generalized parameter-shift rule.
This is now proved in `QuantumAlg.Util.DirichletKernel` at coefficient level and assembled
here for the abstract trigonometric polynomial `genTrigCost`. -/
theorem dirichlet_first_identity (a b : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) :
    ∑ μ ∈ Finset.Icc 1 (2 * R), genTrigCost a b R (psPoint R μ) * psWeight R μ
      = ∑ p ∈ Finset.Icc 1 R, (p : ℝ) * b p := by
  unfold genTrigCost
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
        (a 0 + ∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint R μ)
          + b p * Real.sin ((p : ℝ) * psPoint R μ))) * psWeight R μ)
      =
        ∑ μ ∈ Finset.Icc 1 (2 * R),
          (a 0 * psWeight R μ
            + (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint R μ)
              + b p * Real.sin ((p : ℝ) * psPoint R μ))) * psWeight R μ) by
      exact Finset.sum_congr rfl fun μ _ => by ring]
  rw [Finset.sum_add_distrib]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R), a 0 * psWeight R μ)
      = a 0 * ∑ μ ∈ Finset.Icc 1 (2 * R), psWeight R μ by
      rw [Finset.mul_sum]]
  rw [sum_psWeight_eq_zero R hR, mul_zero, zero_add]
  rw [show (∑ μ ∈ Finset.Icc 1 (2 * R),
        (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint R μ)
          + b p * Real.sin ((p : ℝ) * psPoint R μ))) * psWeight R μ)
      =
        ∑ p ∈ Finset.Icc 1 R,
          (a p * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos ((p : ℝ) * psPoint R μ) * psWeight R μ
            + b p * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.sin ((p : ℝ) * psPoint R μ) * psWeight R μ) by
      calc
        (∑ μ ∈ Finset.Icc 1 (2 * R),
          (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint R μ)
            + b p * Real.sin ((p : ℝ) * psPoint R μ))) * psWeight R μ)
            =
          ∑ μ ∈ Finset.Icc 1 (2 * R),
            ∑ p ∈ Finset.Icc 1 R,
              (a p * Real.cos ((p : ℝ) * psPoint R μ)
                + b p * Real.sin ((p : ℝ) * psPoint R μ)) * psWeight R μ := by
          apply Finset.sum_congr rfl
          intro μ _
          rw [Finset.sum_mul]
        _ = ∑ p ∈ Finset.Icc 1 R,
            ∑ μ ∈ Finset.Icc 1 (2 * R),
              (a p * Real.cos ((p : ℝ) * psPoint R μ)
                + b p * Real.sin ((p : ℝ) * psPoint R μ)) * psWeight R μ := by
          rw [Finset.sum_comm]
        _ = ∑ p ∈ Finset.Icc 1 R,
          (a p * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.cos ((p : ℝ) * psPoint R μ) * psWeight R μ
            + b p * ∑ μ ∈ Finset.Icc 1 (2 * R),
              Real.sin ((p : ℝ) * psPoint R μ) * psWeight R μ) := by
          apply Finset.sum_congr rfl
          intro p _
          rw [Finset.sum_congr rfl (fun μ _ => by ring :
            ∀ μ ∈ Finset.Icc 1 (2 * R),
              (a p * Real.cos ((p : ℝ) * psPoint R μ)
                + b p * Real.sin ((p : ℝ) * psPoint R μ)) * psWeight R μ
                =
                  a p * (Real.cos ((p : ℝ) * psPoint R μ) * psWeight R μ)
                  + b p * (Real.sin ((p : ℝ) * psPoint R μ) * psWeight R μ))]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp1, hpR⟩ := Finset.mem_Icc.mp hp
  rw [sum_cos_mul_psWeight_eq_zero R p hR, sum_sin_mul_psWeight_eq R p hR hp1 hpR]
  ring

/-- The even-node Dirichlet identity used by the second generalized parameter-shift rule.
This assembles the coefficient-level identities proved in `QuantumAlg.Util.DirichletKernel`
for the abstract trigonometric polynomial `genTrigCost`. -/
theorem dirichlet_second_identity (a b : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) :
    -genTrigCost a b R 0 * (2 * (R : ℝ) ^ 2 + 1) / 6
        + ∑ μ ∈ Finset.Icc 1 (2 * R - 1), genTrigCost a b R (psPoint2 R μ) * psWeight2 R μ
      = -∑ p ∈ Finset.Icc 1 R, (p : ℝ) ^ 2 * a p := by
  let C : ℝ := (2 * (R : ℝ) ^ 2 + 1) / 6
  rw [show -genTrigCost a b R 0 * (2 * (R : ℝ) ^ 2 + 1) / 6
      = -genTrigCost a b R 0 * C by
      simp [C]
      ring]
  change -genTrigCost a b R 0 * C
        + ∑ μ ∈ Finset.Icc 1 (2 * R - 1), genTrigCost a b R (psPoint2 R μ) * psWeight2 R μ
      = -∑ p ∈ Finset.Icc 1 R, (p : ℝ) ^ 2 * a p
  have hzero : genTrigCost a b R 0 = a 0 + ∑ p ∈ Finset.Icc 1 R, a p := by
    unfold genTrigCost
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, add_zero]
  have hweighted :
      ∑ μ ∈ Finset.Icc 1 (2 * R - 1), genTrigCost a b R (psPoint2 R μ) * psWeight2 R μ
        = a 0 * C + ∑ p ∈ Finset.Icc 1 R, a p * (C - (p : ℝ) ^ 2) := by
    unfold genTrigCost
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (a 0 + ∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
            + b p * Real.sin ((p : ℝ) * psPoint2 R μ))) * psWeight2 R μ)
        =
          ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            (a 0 * psWeight2 R μ
              + (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
                + b p * Real.sin ((p : ℝ) * psPoint2 R μ))) * psWeight2 R μ) by
        exact Finset.sum_congr rfl fun μ _ => by ring]
    rw [Finset.sum_add_distrib]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1), a 0 * psWeight2 R μ)
        = a 0 * ∑ μ ∈ Finset.Icc 1 (2 * R - 1), psWeight2 R μ by
        rw [Finset.mul_sum]]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1), psWeight2 R μ) = C by
      simpa [C] using sum_psWeight2_eq R hR]
    rw [show (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
          (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
            + b p * Real.sin ((p : ℝ) * psPoint2 R μ))) * psWeight2 R μ)
        =
          ∑ p ∈ Finset.Icc 1 R,
            (a p * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ
              + b p * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.sin ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ) by
        calc
          (∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            (∑ p ∈ Finset.Icc 1 R, (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
              + b p * Real.sin ((p : ℝ) * psPoint2 R μ))) * psWeight2 R μ)
              =
            ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
              ∑ p ∈ Finset.Icc 1 R,
                (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
                  + b p * Real.sin ((p : ℝ) * psPoint2 R μ)) * psWeight2 R μ := by
            apply Finset.sum_congr rfl
            intro μ _
            rw [Finset.sum_mul]
          _ = ∑ p ∈ Finset.Icc 1 R,
              ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
                  + b p * Real.sin ((p : ℝ) * psPoint2 R μ)) * psWeight2 R μ := by
            rw [Finset.sum_comm]
          _ = ∑ p ∈ Finset.Icc 1 R,
            (a p * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.cos ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ
              + b p * ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
                Real.sin ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_congr rfl (fun μ _ => by ring :
              ∀ μ ∈ Finset.Icc 1 (2 * R - 1),
                (a p * Real.cos ((p : ℝ) * psPoint2 R μ)
                  + b p * Real.sin ((p : ℝ) * psPoint2 R μ)) * psWeight2 R μ
                  =
                    a p * (Real.cos ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ)
                    + b p * (Real.sin ((p : ℝ) * psPoint2 R μ) * psWeight2 R μ))]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]]
    apply congrArg (fun t => a 0 * C + t)
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hp1, hpR⟩ := Finset.mem_Icc.mp hp
    rw [sum_cos_mul_psWeight2_eq R p hR hp1 hpR, sum_sin_mul_psWeight2_eq_zero R p hR]
    ring
  rw [hweighted, hzero]
  rw [show (∑ p ∈ Finset.Icc 1 R, a p * (C - (p : ℝ) ^ 2))
      = C * ∑ p ∈ Finset.Icc 1 R, a p
        - ∑ p ∈ Finset.Icc 1 R, (p : ℝ) ^ 2 * a p by
      rw [show (∑ p ∈ Finset.Icc 1 R, a p * (C - (p : ℝ) ^ 2))
          = ∑ p ∈ Finset.Icc 1 R, (C * a p - (p : ℝ) ^ 2 * a p) by
          exact Finset.sum_congr rfl fun p _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]]
  ring

/-- **Generalized parameter-shift data** (Wierichs et al. 2022, Sec. 3.4). The trigonometric
polynomial coefficients; the required Dirichlet-kernel identities are proved in
`QuantumAlg.Util.DirichletKernel` and assembled above for `genTrigCost`. -/
structure GeneralizedParamShift (R : ℕ) where
  /-- Cosine coefficients (`a 0` is the constant term). -/
  a : ℕ → ℝ
  /-- Sine coefficients. -/
  b : ℕ → ℝ
  /-- At least one frequency. -/
  hR : 1 ≤ R

namespace GeneralizedParamShift

variable {R : ℕ} (G : GeneralizedParamShift R)

/-- **Generalized parameter-shift rule (first derivative).** The exact gradient `ℓ'(0)` equals
the `2R`-point weighted sum of shifted evaluations. Combines the genuine derivative
`genTrigCost_deriv_zero` with the proved Dirichlet identity. -/
theorem firstDeriv :
    deriv (genTrigCost G.a G.b R) 0
      = ∑ μ ∈ Finset.Icc 1 (2 * R), genTrigCost G.a G.b R (psPoint R μ) * psWeight R μ := by
  rw [genTrigCost_deriv_zero, ← dirichlet_first_identity G.a G.b R G.hR]

/-- **Generalized parameter-shift rule (second derivative).** The exact curvature `ℓ''(0)`
equals the weighted sum of shifted evaluations. -/
theorem secondDeriv :
    deriv (deriv (genTrigCost G.a G.b R)) 0
      = -genTrigCost G.a G.b R 0 * (2 * (R : ℝ) ^ 2 + 1) / 6
        + ∑ μ ∈ Finset.Icc 1 (2 * R - 1),
            genTrigCost G.a G.b R (psPoint2 R μ) * psWeight2 R μ := by
  rw [genTrigCost_deriv2_zero, ← dirichlet_second_identity G.a G.b R G.hR]

end GeneralizedParamShift

/-- **Non-vacuity.** A concrete nonzero trigonometric polynomial exists at `R = 1`. -/
theorem generalizedParamShift_nonempty : Nonempty (GeneralizedParamShift 1) :=
  ⟨{ a := fun p => if p = 1 then 1 else 0
     b := fun p => if p = 1 then 1 else 0
     hR := le_refl 1 }⟩

end

end QuantumAlg
