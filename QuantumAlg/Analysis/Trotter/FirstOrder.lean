/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Analysis.Trotter.Commuting
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite-family first-order Trotter error bounds

The noncommuting estimate follows by differentiating an interpolation, applying
the fundamental theorem of calculus, and integrating the commutator bound
[Lin22, trotter.tex:88-115]. For nonnegative time the one-step constant is
`t² / 2`; telescoping unitary products gives `t² / (2r)` for `r > 0`.
The descending finite-family formula retains the norm of each tail-sum
commutator and the same sharp prefactor [CST+21, prefactor.tex:45-50].
Simultaneous sign reversal extends this bound to all real times.
These are operator-norm estimates; no circuit or resource claim is made.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

namespace TrotterOneStepErrorBound

/-- The sharp two-term one-step commutator bound right-hand side. -/
def commutatorBoundRhs {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) : ℝ :=
  (t ^ 2 / 2) *
    opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆)

lemma commutatorBoundRhs_nonneg {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    0 ≤ commutatorBoundRhs H₁ H₂ t := by
  unfold commutatorBoundRhs
  exact mul_nonneg (div_nonneg (sq_nonneg t) (by norm_num))
    (opNorm_nonneg (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆))

@[simp]
lemma commutatorBoundRhs_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    commutatorBoundRhs H₁ H₂ t = 0 := by
  unfold commutatorBoundRhs
  rw [hcomm.lie_eq, opNorm_zero, mul_zero]

/-- The target noncommuting one-step commutator error estimate.

This auxiliary proposition includes the nonnegative-time premise. The public
error theorem below derives it from the Duhamel/FTC matrix-exponential proof. -/
def Statement {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) : Prop :=
  0 ≤ t →
    opNorm
        (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
          - firstOrderTrotterStepOp
              (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t)
      ≤ commutatorBoundRhs H₁ H₂ t

/-- The one-step additive error of the two-term first-order Trotter formula. -/
def oneStepErrorOp {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
    - firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t

lemma statement_iff_oneStepErrorOp {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    Statement H₁ H₂ t ↔
      0 ≤ t →
        opNorm (oneStepErrorOp H₁ H₂ t)
          ≤ commutatorBoundRhs H₁ H₂ t := by
  rfl

/-- The interpolation between exact two-term evolution and one Trotter step. -/
private def interpolationOp {R : Register} (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) (t - s)
    * firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) s

@[simp]
private lemma interpolationOp_zero {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    interpolationOp H₁ H₂ t 0
      = timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t := by
  simp [interpolationOp, firstOrderTrotterStepOp, timeEvolutionOp]

@[simp]
private lemma interpolationOp_self {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    interpolationOp H₁ H₂ t t
      = firstOrderTrotterStepOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t := by
  simp [interpolationOp, timeEvolutionOp]

/-- The one-step error is the difference between the interpolation endpoints. -/
private lemma oneStepErrorOp_eq_interpolation_endpoints {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    oneStepErrorOp H₁ H₂ t = interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t := by
  simp [oneStepErrorOp]

/-- Norm form of the interpolation endpoint identity. -/
private lemma opNorm_oneStepErrorOp_eq_interpolation_endpoints {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    opNorm (oneStepErrorOp H₁ H₂ t)
      = opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t) := by
  rw [oneStepErrorOp_eq_interpolation_endpoints]

/-- An analytic endpoint estimate for the interpolation implies the target
one-step Trotter bound. -/
private lemma statement_of_interpolation_endpoints_bound {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ)
    (hbound :
      opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t)
        ≤ commutatorBoundRhs H₁ H₂ t) :
    Statement H₁ H₂ t := by
  rw [statement_iff_oneStepErrorOp]
  intro _ht
  rw [opNorm_oneStepErrorOp_eq_interpolation_endpoints]
  exact hbound

/-- Named Duhamel/FTC endpoint estimate for the two-term interpolation.

This intermediate estimate in the noncommuting one-step proof states that the
interpolation endpoint difference is bounded by the
sharp commutator right-hand side. -/
private structure DuhamelEndpointEstimate {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    Prop where
  endpointBound :
    opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t)
      ≤ commutatorBoundRhs H₁ H₂ t

/-- The Duhamel/FTC endpoint estimate implies the one-step commutator error bound. -/
private lemma bound_of_duhamelEndpointEstimate {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ)
    (hduhamel : DuhamelEndpointEstimate H₁ H₂ t) :
    Statement H₁ H₂ t :=
  statement_of_interpolation_endpoints_bound H₁ H₂ t hduhamel.endpointBound

/-- The three-term product-rule derivative of `interpolationOp`. -/
private def interpolationDerivativeOp {R : Register} (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    HilbertOperator R :=
  let Hsum : HilbertOperator R :=
    (H₁ : HilbertOperator R) + (H₂ : HilbertOperator R);
  -(timeEvolutionOp Hsum (t - s) * ((-Complex.I) • Hsum))
    * firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) s
    + timeEvolutionOp Hsum (t - s)
      * ((timeEvolutionOp (H₁ : HilbertOperator R) s * ((-Complex.I) • (H₁ : HilbertOperator R)))
          * timeEvolutionOp (H₂ : HilbertOperator R) s
        + timeEvolutionOp (H₁ : HilbertOperator R) s
          * (timeEvolutionOp (H₂ : HilbertOperator R) s
              * ((-Complex.I) • (H₂ : HilbertOperator R))))

/-- The commutator kernel that appears in the two-term Lie-Trotter Duhamel
integral, with unitary evolution factors on both sides. -/
def commutatorKernel {R : Register} (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) (t - s)
    * ⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆
    * firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) s

/-- The unitary factors in the commutator kernel do not change the operator norm. -/
lemma opNorm_commutatorKernel {R : Register}
    (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    opNorm (commutatorKernel H₁ H₂ t s)
      = opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  unfold commutatorKernel
  rw [mul_assoc]
  rw [opNorm_unitaryGroup_mul
    (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆
      * firstOrderTrotterStepOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) s)
    (timeEvolutionOp_mem_unitaryGroup (H₁.2.add H₂.2) (t - s))]
  rw [opNorm_mul_unitaryGroup
    (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆)
    (firstOrderTrotterStepOp_mem_unitaryGroup H₁ H₂ s)]

/-- The commutator kernel is uniformly bounded by the commutator norm. -/
lemma opNorm_commutatorKernel_le {R : Register}
    (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    opNorm (commutatorKernel H₁ H₂ t s)
      ≤ opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  rw [opNorm_commutatorKernel H₁ H₂ t s]

/-- The commutator kernel vanishes on the commuting boundary. -/
lemma commutatorKernel_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t s : ℝ) :
    commutatorKernel H₁ H₂ t s = 0 := by
  simp [commutatorKernel, hcomm.lie_eq]

@[simp]
lemma opNorm_commutatorKernel_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t s : ℝ) :
    opNorm (commutatorKernel H₁ H₂ t s) = 0 := by
  rw [commutatorKernel_eq_zero_of_commute H₁ H₂ hcomm t s, opNorm_zero]

/-- One-step exactness on the commuting boundary.  The noncommuting
commutator-norm estimate is proved below. -/
lemma commuting_boundary_eq {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
      = firstOrderTrotterStepOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t :=
  timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute hcomm t

/-- On the commuting boundary, the interpolation endpoints coincide. -/
private lemma interpolation_endpoints_sub_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t = 0 := by
  rw [interpolationOp_zero, interpolationOp_self, commuting_boundary_eq H₁ H₂ hcomm t,
    sub_self]

private lemma opNorm_interpolation_endpoints_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t) = 0 := by
  rw [interpolation_endpoints_sub_eq_zero_of_commute H₁ H₂ hcomm t, opNorm_zero]

/-- The Duhamel endpoint estimate is witnessed on the commuting boundary. -/
private lemma duhamelEndpointEstimate_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    DuhamelEndpointEstimate H₁ H₂ t := by
  refine ⟨?_⟩
  rw [opNorm_interpolation_endpoints_eq_zero_of_commute H₁ H₂ hcomm t]
  exact commutatorBoundRhs_nonneg H₁ H₂ t

/-- The commutator-norm error bound is trivial on the commuting boundary. -/
lemma commuting_boundary_operatorNorm {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) : Statement H₁ H₂ t := by
  unfold Statement
  intro _ht
  rw [commuting_boundary_eq H₁ H₂ hcomm t, sub_self, opNorm_zero]
  exact commutatorBoundRhs_nonneg H₁ H₂ t

/-! ### Two-step Duhamel integration: noncommuting one-step error bound

The Duhamel/FTC proof uses two nested FTC applications [Lin22, trotter.tex:88-115].
1. Outer FTC: F(s) = interpolationOp(s) → error = F(0)-F(t) = ∫₀ᵗ F'(s) ds
2. Inner FTC: G(u) = e^(uA)·H₂·e^(-uA) → ‖H₂·e^(sA) - e^(sA)·H₂‖ ≤ s·‖[H₁,H₂]‖
3. Combine: ‖error‖ ≤ (t²/2)·‖[H₁,H₂]‖

The infrastructure (derivatives, commutator kernel, unitary norm invariance)
is combined below with two calculus lemmas to prove the endpoint estimate. -/

open scoped Interval

/-- The derivative of `interpolationOp` equals `interpolationDerivativeOp`.

Uses `HasDerivAt.scomp` (chain rule for scalar domain), `HasDerivAt.mul`
(product rule), and `hasDerivAt_timeEvolutionOp` for each factor. -/
private lemma hasDerivAt_interpolationOp {R : Register} (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    HasDerivAt (fun s => interpolationOp H₁ H₂ t s)
      (interpolationDerivativeOp H₁ H₂ t s) s := by
  open scoped Matrix.Norms.L2Operator in
  -- Separate: calculus derivation → algebraic simplification
  let Hsum : HilbertOperator R := (H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)
  let A : HilbertOperator R := (-Complex.I) • Hsum
  let B' : HilbertOperator R := (-Complex.I) • (H₁ : HilbertOperator R)
  let C' : HilbertOperator R := (-Complex.I) • (H₂ : HilbertOperator R)
  -- Chain rule: d/ds [timeEvolutionOp Hsum (t-s)]
  have hsum_deriv : HasDerivAt (fun u : ℝ => timeEvolutionOp Hsum u)
    (timeEvolutionOp Hsum (t - s) * A) (t - s) := by
    simpa [A] using hasDerivAt_timeEvolutionOp Hsum (t - s)
  have h_const_sub : HasDerivAt (fun x : ℝ => t - x) (-1) s :=
    (hasDerivAt_id s).const_sub t
  have hA : HasDerivAt (fun s' : ℝ => timeEvolutionOp Hsum (t - s'))
    ((-1 : ℝ) • (timeEvolutionOp Hsum (t - s) * A)) s :=
    HasDerivAt.scomp s hsum_deriv h_const_sub
  -- Derivatives for TE₁ and TE₂
  have hB : HasDerivAt (fun s' : ℝ => timeEvolutionOp (H₁ : HilbertOperator R) s')
    (timeEvolutionOp (H₁ : HilbertOperator R) s * B') s := by
    simpa [B'] using hasDerivAt_timeEvolutionOp (H₁ : HilbertOperator R) s
  have hC : HasDerivAt (fun s' : ℝ => timeEvolutionOp (H₂ : HilbertOperator R) s')
    (timeEvolutionOp (H₂ : HilbertOperator R) s * C') s := by
    simpa [C'] using hasDerivAt_timeEvolutionOp (H₂ : HilbertOperator R) s
  -- Shorthand for operator values at point s (reduces long lines below)
  let TE₁_s : HilbertOperator R := timeEvolutionOp (H₁ : HilbertOperator R) s
  let TE₂_s : HilbertOperator R := timeEvolutionOp (H₂ : HilbertOperator R) s
  let TE_sum_s : HilbertOperator R := timeEvolutionOp Hsum (t - s)
  -- Product rule: (TE₁ * TE₂)' = TE₁'*TE₂ + TE₁*TE₂'
  have hBC : HasDerivAt
    (fun s' : ℝ =>
      timeEvolutionOp (H₁ : HilbertOperator R) s' * timeEvolutionOp (H₂ : HilbertOperator R) s')
    ((TE₁_s * B') * TE₂_s + TE₁_s * (TE₂_s * C')) s :=
    HasDerivAt.mul hB hC
  -- Product rule: (A * (B*C))'
  have hABC : HasDerivAt
    (fun s' : ℝ =>
      timeEvolutionOp Hsum (t - s')
        * (timeEvolutionOp (H₁ : HilbertOperator R) s'
            * timeEvolutionOp (H₂ : HilbertOperator R) s'))
    (((-1 : ℝ) • (TE_sum_s * A)) * (TE₁_s * TE₂_s)
      + TE_sum_s * ((TE₁_s * B') * TE₂_s + TE₁_s * (TE₂_s * C'))) s :=
    HasDerivAt.mul hA hBC
  -- Use HasDerivAt.congr_deriv to decouple calculus from algebra
  apply HasDerivAt.congr_deriv hABC
  dsimp [interpolationOp, interpolationDerivativeOp, firstOrderTrotterStepOp,
    Hsum, A, B', C', TE₁_s, TE₂_s, TE_sum_s]
  -- Pure matrix algebra: neg_one_smul eliminates (-1 : ℝ) •, mul_assoc normalizes parens
  simp [neg_one_smul ℝ, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, smul_add]

/-! ### Infrastructure for the inner commutator bound (Lemma 2) -/

/-- A Hamiltonian commutes with its own time-evolution operator.
This is the algebraic heart of the inner bound: `H` and `exp(-i*u*H)` commute. -/
lemma commute_H_timeEvolutionOp {R : Register} (H : HilbertOperator R) (u : ℝ) :
    Commute H (timeEvolutionOp H u) := by
  -- `timeEvolutionOp H u` expands to `exp ((-(Complex.I * u)) * H)`
  -- `H` trivially commutes with any scalar multiple of itself
  have h_comm_smul : Commute H ((-(Complex.I * (u : ℂ))) • H) :=
    (Commute.refl H).smul_right _
  -- `Commute.exp_right` lifts commuting from the exponent to the exponential
  unfold timeEvolutionOp
  exact h_comm_smul.exp_right

/-- The time-evolution operator is continuous in the time parameter.
This yields `IntervalIntegrable` via `Continuous.intervalIntegrable`. -/
lemma continuous_timeEvolutionOp {R : Register} (H : HilbertOperator R) :
    Continuous (fun u : ℝ => timeEvolutionOp H u) := by
  -- Derive continuity from differentiability: `HasDerivAt` → `ContinuousAt`
  open scoped Matrix.Norms.L2Operator in
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hasDerivAt_timeEvolutionOp H x).continuousAt

/-- Group property: `TE(t) * TE(-t) = 1`. Follows from `exp(A)*exp(-A) = exp(0) = 1`. -/
lemma timeEvolutionOp_mul_neg {R : Register} (H : HilbertOperator R) (t : ℝ) :
    timeEvolutionOp H t * timeEvolutionOp H (-t) = 1 := by
  rw [timeEvolutionOp, timeEvolutionOp]
  have hAB : Commute ((-(Complex.I * (t : ℂ))) • H) ((-(Complex.I * ((-t) : ℂ))) • H) :=
    ((Commute.refl H).smul_left
      (-(Complex.I * (t : ℂ)))).smul_right (-(Complex.I * ((-t) : ℂ)))
  have h_sum : (-(Complex.I * (t : ℂ))) • H + (-(Complex.I * ((-t) : ℂ))) • H = 0 := by
    calc
      (-(Complex.I * (t : ℂ))) • H + (-(Complex.I * ((-t) : ℂ))) • H
          = ((-(Complex.I * (t : ℂ))) + (-(Complex.I * ((-t) : ℂ)))) • H := by rw [← add_smul]
      _ = (0 : ℂ) • H := by
        ring_nf
      _ = 0 := by simp
  have h_exp := Matrix.exp_add_of_commute
    ((-(Complex.I * (t : ℂ))) • H) ((-(Complex.I * ((-t) : ℂ))) • H) hAB
  -- h_exp : exp(A + B) = exp A * exp B, so we rewrite via .symm
  simpa [h_sum] using h_exp.symm

/-- Auxiliary function for the inner FTC: `G(u) = TE1(u) * H2 * TE1(-u)`. -/
noncomputable def gFunc {R : Register} (H₁ H₂ : HilbertOperator R) (u : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp H₁ u * H₂ * timeEvolutionOp H₁ (-u)

/-- Derivative of `gFunc`: `G'(u) = (-i) * TE1(u) * [H1,H2] * TE1(-u)`. -/
noncomputable def gDeriv {R : Register} (H₁ H₂ : HilbertOperator R) (u : ℝ) :
    HilbertOperator R :=
  (-Complex.I : ℂ) • (timeEvolutionOp H₁ u * ⁅H₁, H₂⁆ * timeEvolutionOp H₁ (-u))

/-- `gDeriv` is continuous, hence `IntervalIntegrable` on compact intervals. -/
lemma continuous_gDeriv {R : Register} (H₁ H₂ : HilbertOperator R) :
    Continuous (fun u : ℝ => gDeriv H₁ H₂ u) := by
  open scoped Matrix.Norms.L2Operator in
  unfold gDeriv
  exact (((continuous_timeEvolutionOp H₁).mul continuous_const).mul
    ((continuous_timeEvolutionOp H₁).comp continuous_neg)).const_smul (-Complex.I : ℂ)

/-- `gFunc` has derivative `gDeriv`.  Uses the three-factor product rule
`HasDerivAt.mul` twice, plus `HasDerivAt.scomp` (chain rule for `u |-> -u`),
and `commute_H_timeEvolutionOp` to factor the commutator. -/
lemma hasDerivAt_gFunc {R : Register} (H₁ H₂ : HilbertOperator R) (u : ℝ) :
    HasDerivAt (gFunc H₁ H₂) (gDeriv H₁ H₂ u) u := by
  let A : HilbertOperator R := (-Complex.I) • H₁
  have h_comm : Commute H₁ (timeEvolutionOp H₁ u) := commute_H_timeEvolutionOp H₁ u
  have h_comm_neg : Commute H₁ (timeEvolutionOp H₁ (-u)) := commute_H_timeEvolutionOp H₁ (-u)
  have hC_inner : HasDerivAt (fun x : ℝ => -x) (-1) u := hasDerivAt_neg u
  open scoped Matrix.Norms.L2Operator in
  have hB : HasDerivAt (fun _ : ℝ => H₂) 0 u := hasDerivAt_const _ _
  have hA : HasDerivAt (fun s : ℝ => timeEvolutionOp H₁ s)
    (timeEvolutionOp H₁ u * A) u := by
    simpa [A] using hasDerivAt_timeEvolutionOp H₁ u
  have hC_outer : HasDerivAt (fun v : ℝ => timeEvolutionOp H₁ v)
    (timeEvolutionOp H₁ (-u) * A) (-u) := by
    simpa [A] using hasDerivAt_timeEvolutionOp H₁ (-u)
  have hC : HasDerivAt (fun x : ℝ => timeEvolutionOp H₁ (-x))
    ((-1 : ℝ) • (timeEvolutionOp H₁ (-u) * A)) u :=
    HasDerivAt.scomp u hC_outer hC_inner
  have hAB_mul := HasDerivAt.mul hA hB
  -- hAB_mul : HasDerivAt (TE₁ * H₂) (TE₁ u * A * H₂ + TE₁ u * 0) u
  -- Clean up the + 0 in the derivative
  have hAB_clean : HasDerivAt (fun s : ℝ => timeEvolutionOp H₁ s * H₂)
    ((timeEvolutionOp H₁ u * A) * H₂) u :=
    hAB_mul.congr_deriv (by simp [add_zero])
  have hABC_mul := HasDerivAt.mul hAB_clean hC
  apply HasDerivAt.congr_deriv hABC_mul
  -- Pure algebra: simplify messy derivative to gDeriv H₁ H₂ u
  simp [gDeriv, Ring.lie_def, A, neg_one_smul ℝ, Matrix.mul_assoc,
    h_comm_neg.symm.eq, mul_neg, add_mul, mul_add, smul_add, sub_eq_add_neg]

/-- Core FTC bound: `|G(s) - G(0)| <= s * |[H1, H2]|`.
Uses `integral_eq_sub_of_hasDerivAt` (FTC) and
`norm_integral_le_integral_norm` (Bochner integral norm inequality). -/
lemma G_diff_norm_bound {R : Register}
    (H₁ H₂ : HilbertOperator R) (hH₁ : H₁.IsHermitian) (s : ℝ) (hs : 0 ≤ s) :
    opNorm (gFunc H₁ H₂ s - gFunc H₁ H₂ 0)
    ≤ s * opNorm (⁅H₁, H₂⁆) := by
  open scoped Matrix.Norms.L2Operator in
  -- FTC: G(s) - G(0) = ∫[0,s] G'(u) du
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) s, HasDerivAt
    (gFunc H₁ H₂) (gDeriv H₁ H₂ x) x :=
    fun x _ => hasDerivAt_gFunc H₁ H₂ x
  have h_int : IntervalIntegrable (gDeriv H₁ H₂) MeasureTheory.volume (0 : ℝ) s :=
    (continuous_gDeriv H₁ H₂).intervalIntegrable (0 : ℝ) s
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  -- h_ftc : ∫ y in (0:ℝ)..s, gDeriv H₁ H₂ y = gFunc H₁ H₂ s - gFunc H₁ H₂ 0
  rw [← h_ftc]
  -- Now: |∫ G'(u) du| ≤ ∫ |G'(u)| du
  have h_norm_int : ‖∫ u in (0 : ℝ)..s, gDeriv H₁ H₂ u‖ ≤
      ∫ u in (0 : ℝ)..s, ‖gDeriv H₁ H₂ u‖ :=
    intervalIntegral.norm_integral_le_integral_norm (f := gDeriv H₁ H₂) hs
  refine le_trans h_norm_int ?_
  -- Bound the integrand: |G'(u)| = |[H1,H2]| by unitary invariance of TE1
  have h_integrand : ∀ v, ‖gDeriv H₁ H₂ v‖ = opNorm (⁅H₁, H₂⁆) := by
    intro v
    have h_unitary_v : timeEvolutionOp H₁ v ∈ Matrix.unitaryGroup R.Index ℂ :=
      timeEvolutionOp_mem_unitaryGroup hH₁ v
    have h_unitary_negv : timeEvolutionOp H₁ (-v) ∈ Matrix.unitaryGroup R.Index ℂ :=
      timeEvolutionOp_mem_unitaryGroup hH₁ (-v)
    unfold gDeriv opNorm
    open scoped Matrix.Norms.L2Operator in
    calc
      ‖(-Complex.I : ℂ) • (timeEvolutionOp H₁ v * ⁅H₁, H₂⁆ * timeEvolutionOp H₁ (-v))‖
        = ‖(-Complex.I : ℂ)‖
          * ‖timeEvolutionOp H₁ v * ⁅H₁, H₂⁆ * timeEvolutionOp H₁ (-v)‖ := by
        rw [norm_smul]
      _ = 1 * ‖timeEvolutionOp H₁ v * ⁅H₁, H₂⁆ * timeEvolutionOp H₁ (-v)‖ := by
        simp
      _ = ‖timeEvolutionOp H₁ v * ⁅H₁, H₂⁆ * timeEvolutionOp H₁ (-v)‖ := by simp
      _ = ‖(timeEvolutionOp H₁ v * ⁅H₁, H₂⁆) * timeEvolutionOp H₁ (-v)‖ := by
        simp [Matrix.mul_assoc]
      _ = ‖timeEvolutionOp H₁ v * ⁅H₁, H₂⁆‖ := by
        simpa [opNorm] using
          congrArg (fun x : ℝ => x) (opNorm_mul_unitaryGroup
            (timeEvolutionOp H₁ v * ⁅H₁, H₂⁆) h_unitary_negv)
      _ = ‖⁅H₁, H₂⁆‖ := by
        simpa [opNorm] using
          congrArg (fun x : ℝ => x) (opNorm_unitaryGroup_mul
            (⁅H₁, H₂⁆) h_unitary_v)
  have h_bound : (∫ u in (0 : ℝ)..s, ‖gDeriv H₁ H₂ u‖)
      ≤ (∫ u in (0 : ℝ)..s, opNorm (⁅H₁, H₂⁆)) := by
    refine intervalIntegral.integral_mono hs ?_ ?_ ?_
    · exact (continuous_gDeriv H₁ H₂).norm.intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
    · intro u
      simp [h_integrand u]
  refine le_trans h_bound ?_
  simp [intervalIntegral.integral_const]

/-- Inner commutator norm bound:
`|H2*exp(sA) - exp(sA)*H2| <= s*|[H1, H2]|` where `A = -i*H1`.

Right-multiplication identity:
`H2*TE(s) - TE(s)*H2 = (G(0) - G(s)) * TE(s)`
then apply `G_diff_norm_bound` + unitary norm invariance. -/
lemma inner_commutator_norm_bound {R : Register}
    (H₁ : Hamiltonian R) (H₂ : HilbertOperator R) (s : ℝ) (hs : 0 ≤ s) :
    opNorm ((H₂ : HilbertOperator R) * timeEvolutionOp (H₁ : HilbertOperator R) s
      - timeEvolutionOp (H₁ : HilbertOperator R) s * (H₂ : HilbertOperator R))
    ≤ s * opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  let H₁' : HilbertOperator R := (H₁ : HilbertOperator R)
  let H₂' : HilbertOperator R := (H₂ : HilbertOperator R)
  have hH₁_herm : H₁'.IsHermitian := H₁.2
  have h_unitary_s : timeEvolutionOp H₁' s ∈ Matrix.unitaryGroup R.Index ℂ :=
    timeEvolutionOp_mem_unitaryGroup hH₁_herm s
  have hG0 : gFunc H₁' H₂' 0 = H₂' := by
    simp [gFunc, timeEvolutionOp]
  -- Key identity: H₂*TE(s) - TE(s)*H₂ = (G(0) - G(s)) * TE(s)
  -- Use ext i j to reduce matrix equality to scalar algebra
  -- TE(t) * TE(-t) = 1 (and TE(-t) * TE(t) = 1), from exp(A+B) = exp(A)*exp(B)
  have hTE_prod : timeEvolutionOp H₁' s * timeEvolutionOp H₁' (-s) = 1 :=
    timeEvolutionOp_mul_neg H₁' s
  have hTE_prod_rev : timeEvolutionOp H₁' (-s) * timeEvolutionOp H₁' s = 1 := by
    simpa [neg_neg] using timeEvolutionOp_mul_neg H₁' (-s)
  have h_algebra : H₂' * timeEvolutionOp H₁' s - timeEvolutionOp H₁' s * H₂'
      = (gFunc H₁' H₂' 0 - gFunc H₁' H₂' s) * timeEvolutionOp H₁' s := by
    calc
      H₂' * timeEvolutionOp H₁' s - timeEvolutionOp H₁' s * H₂'
          = H₂' * timeEvolutionOp H₁' s
            - timeEvolutionOp H₁' s * H₂'
              * (timeEvolutionOp H₁' (-s) * timeEvolutionOp H₁' s) := by
        rw [hTE_prod_rev, mul_one]
      _ = H₂' * timeEvolutionOp H₁' s
            - (timeEvolutionOp H₁' s * H₂' * timeEvolutionOp H₁' (-s))
              * timeEvolutionOp H₁' s := by
        simp [Matrix.mul_assoc]
      _ = (H₂' - timeEvolutionOp H₁' s * H₂' * timeEvolutionOp H₁' (-s))
            * timeEvolutionOp H₁' s := by
        simp [Matrix.sub_mul, Matrix.sub_mul]
      _ = (gFunc H₁' H₂' 0 - gFunc H₁' H₂' s) * timeEvolutionOp H₁' s := by
        simp [gFunc, timeEvolutionOp]
  rw [h_algebra]
  -- opNorm ((G(0)-G(s)) * TE(s)) = opNorm (G(0)-G(s))
  rw [opNorm_mul_unitaryGroup (gFunc H₁' H₂' 0 - gFunc H₁' H₂' s) h_unitary_s]
  -- opNorm (G(0)-G(s)) = opNorm (G(s)-G(0)) by norm_neg
  have h_eq_sub : gFunc H₁' H₂' 0 - gFunc H₁' H₂' s
      = -(gFunc H₁' H₂' s - gFunc H₁' H₂' 0) := by
    rw [← neg_sub (gFunc H₁' H₂' s) (gFunc H₁' H₂' 0)]
  have h_opnorm_symm : opNorm (gFunc H₁' H₂' 0 - gFunc H₁' H₂' s)
      = opNorm (gFunc H₁' H₂' s - gFunc H₁' H₂' 0) := by
    rw [h_eq_sub]
    exact opNorm_neg _
  rw [h_opnorm_symm]
  exact G_diff_norm_bound H₁' H₂' hH₁_herm s hs

/-- Algebraic simplification of `interpolationDerivativeOp`:
it equals `i·TE_sum(t-s)·(H₂·TE₁(s) - TE₁(s)·H₂)·TE₂(s)`.

Proof: expand definitions → right-assoc flatten → cancel A₁ terms via `Commute A₁ T1`
→ factor commutator → extract scalar `i` via `smul_mul_assoc`/`mul_smul_comm`. -/
private lemma interpolationDerivativeOp_eq {R : Register} (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    interpolationDerivativeOp H₁ H₂ t s
      = (Complex.I : ℂ) • (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R))
            (t - s)
          * ((H₂ : HilbertOperator R) * timeEvolutionOp (H₁ : HilbertOperator R) s
            - timeEvolutionOp (H₁ : HilbertOperator R) s * (H₂ : HilbertOperator R))
          * timeEvolutionOp (H₂ : HilbertOperator R) s) := by
  -- 1. Local abbreviations
  let T_sum := timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) (t - s)
  let T1 := timeEvolutionOp (H₁ : HilbertOperator R) s
  let T2 := timeEvolutionOp (H₂ : HilbertOperator R) s
  let A1 := (-Complex.I : ℂ) • (H₁ : HilbertOperator R)
  let A2 := (-Complex.I : ℂ) • (H₂ : HilbertOperator R)
  -- 2. Commutation lemmas
  have h_comm_A1_T1 : Commute A1 T1 :=
    (commute_H_timeEvolutionOp (H₁ : HilbertOperator R) s).smul_left (-Complex.I : ℂ)
  have h_comm_A2_T2 : Commute A2 T2 :=
    (commute_H_timeEvolutionOp (H₂ : HilbertOperator R) s).smul_left (-Complex.I : ℂ)
  -- 3. Expand LHS definition (dsimp let bindings, then matrix algebra)
  have h_lhs_expand : interpolationDerivativeOp H₁ H₂ t s =
    -(T_sum * A1 * T1 * T2) - (T_sum * A2 * T1 * T2)
      + (T_sum * T1 * A1 * T2) + (T_sum * T1 * T2 * A2) := by
    dsimp [interpolationDerivativeOp, firstOrderTrotterStepOp, T_sum, T1, T2, A1, A2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, neg_mul, smul_add, add_assoc,
      neg_add, sub_eq_add_neg]
  -- 4. A₁ commutes with T1 → cancel A₁ terms
  have h_A1_comm_term : T_sum * T1 * A1 * T2 = T_sum * A1 * T1 * T2 := by
    simp [Matrix.mul_assoc, h_comm_A1_T1.eq]
  have h_lhs_cancel : interpolationDerivativeOp H₁ H₂ t s =
    -(T_sum * A2 * T1 * T2) + (T_sum * T1 * T2 * A2) := by
    rw [h_lhs_expand, h_A1_comm_term]
    abel
  -- 5. A₂ commutes with T2 → factor commutator
  have h_A2_comm_term : T_sum * T1 * T2 * A2 = T_sum * T1 * A2 * T2 := by
    simp [Matrix.mul_assoc, h_comm_A2_T2.eq]
  have h_factor : -(T_sum * A2 * T1 * T2) + (T_sum * T1 * T2 * A2) =
    T_sum * (T1 * A2 - A2 * T1) * T2 := by
    rw [h_A2_comm_term]
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  -- 6. Scalar equivalence: T1*A2 - A2*T1 = i·(H₂*T1 - T1*H₂)
  have h_scalar_eq : T1 * A2 - A2 * T1 =
      (Complex.I : ℂ) • ((H₂ : HilbertOperator R) * T1 - T1 * (H₂ : HilbertOperator R)) := by
    dsimp [A2]
    simp [sub_eq_add_neg, neg_smul, smul_add]
    abel
  -- 7. Assemble: cancel → factor → scalar → extract `i` via smul_mul_assoc
  calc
    interpolationDerivativeOp H₁ H₂ t s
        = -(T_sum * A2 * T1 * T2) + (T_sum * T1 * T2 * A2) := h_lhs_cancel
    _ = T_sum * (T1 * A2 - A2 * T1) * T2 := h_factor
    _ = T_sum * ((Complex.I : ℂ) • ((H₂ : HilbertOperator R) * T1
            - T1 * (H₂ : HilbertOperator R))) * T2 := by
      rw [h_scalar_eq]
    _ = (Complex.I : ℂ) • (T_sum * ((H₂ : HilbertOperator R) * T1
            - T1 * (H₂ : HilbertOperator R)) * T2) := by
      simp

/-- Norm bound for the interpolation derivative:
`‖interpolationDerivativeOp H₁ H₂ t s‖ ≤ s * ‖⁅H₁, H₂⁆‖`.

Uses `interpolationDerivativeOp_eq` to factor out unitary evolution,
then applies `inner_commutator_norm_bound`. -/
private lemma norm_interpolationDerivativeOp_le {R : Register}
    (H₁ H₂ : Hamiltonian R) (t s : ℝ) (hs : 0 ≤ s) :
    opNorm (interpolationDerivativeOp H₁ H₂ t s)
    ≤ s * opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  rw [interpolationDerivativeOp_eq H₁ H₂ t s]
  have hH₁_herm : (H₁ : HilbertOperator R).IsHermitian := H₁.2
  have hH₂_herm : (H₂ : HilbertOperator R).IsHermitian := H₂.2
  have hHsum_herm : ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)).IsHermitian :=
    H₁.2.add H₂.2
  have h_u_sum : timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) (t - s)
      ∈ Matrix.unitaryGroup R.Index ℂ :=
    timeEvolutionOp_mem_unitaryGroup hHsum_herm (t - s)
  have h_u_2 : timeEvolutionOp (H₂ : HilbertOperator R) s
      ∈ Matrix.unitaryGroup R.Index ℂ :=
    timeEvolutionOp_mem_unitaryGroup hH₂_herm s
  let X := ((H₂ : HilbertOperator R) * timeEvolutionOp (H₁ : HilbertOperator R) s
    - timeEvolutionOp (H₁ : HilbertOperator R) s * (H₂ : HilbertOperator R))
  calc
    opNorm ((Complex.I : ℂ) • (timeEvolutionOp ((H₁ : HilbertOperator R)
          + (H₂ : HilbertOperator R)) (t - s)
          * X * timeEvolutionOp (H₂ : HilbertOperator R) s))
        = opNorm (timeEvolutionOp ((H₁ : HilbertOperator R)
            + (H₂ : HilbertOperator R)) (t - s)
            * X * timeEvolutionOp (H₂ : HilbertOperator R) s) := by
      unfold opNorm
      open scoped Matrix.Norms.L2Operator in
      rw [norm_smul]
      simp
    _ = opNorm (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) (t - s)
            * (X * timeEvolutionOp (H₂ : HilbertOperator R) s)) := by
      simp [Matrix.mul_assoc]
    _ = opNorm (X * timeEvolutionOp (H₂ : HilbertOperator R) s) := by
      rw [opNorm_unitaryGroup_mul (X * timeEvolutionOp (H₂ : HilbertOperator R) s) h_u_sum]
    _ = opNorm X := by
      rw [opNorm_mul_unitaryGroup X h_u_2]
    _ ≤ s * opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) :=
      inner_commutator_norm_bound H₁ H₂ s hs

/-- **Duhamel endpoint estimate**: the noncommuting one-step Trotter error is
bounded by `(t²/2)·‖[H₁, H₂]‖`.

The proof combines FTC, unitary cancellation, and the integral of `s` over `[0,t]`. -/
private lemma duhamelEndpointEstimate_proof {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) (ht : 0 ≤ t) :
    DuhamelEndpointEstimate H₁ H₂ t := by
  -- Step 1: FTC — F(0) - F(t) = ∫₀ᵗ F'(s) ds
  have h_deriv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
    (fun s => interpolationOp H₁ H₂ t s)
    (interpolationDerivativeOp H₁ H₂ t s) s :=
    fun s _ => hasDerivAt_interpolationOp H₁ H₂ t s
  -- interpolationDerivativeOp is continuous → interval integrable
  -- Use the same scoping as continuous_gDeriv to get Bochner integrability
  open scoped Matrix.Norms.L2Operator in
  have h_cont : Continuous (fun s : ℝ => interpolationDerivativeOp H₁ H₂ t s) := by
    unfold interpolationDerivativeOp firstOrderTrotterStepOp
    apply Continuous.add
    · -- First term: (-(TE_sum * A_sum)) * (TE₁ * TE₂) — product of two factors
      apply Continuous.mul
      · -- First factor: -(TE_sum * A_sum) — negation of a product
        apply Continuous.neg
        apply Continuous.mul
        · exact (continuous_timeEvolutionOp _).comp (continuous_const.sub continuous_id)
        · exact continuous_const
      · -- Second factor: TE₁ * TE₂
        apply Continuous.mul
        · exact continuous_timeEvolutionOp _
        · exact continuous_timeEvolutionOp _
    · -- Second term: TE_sum(t-s) * ((TE₁(s)*A₁)*TE₂(s) + TE₁(s)*(TE₂(s)*A₂))
      apply Continuous.mul
      · exact (continuous_timeEvolutionOp _).comp (continuous_const.sub continuous_id)
      · apply Continuous.add
        · -- (TE₁(s)*A₁)*TE₂(s)
          apply Continuous.mul
          · apply Continuous.mul
            · exact continuous_timeEvolutionOp _
            · exact continuous_const
          · exact continuous_timeEvolutionOp _
        · -- TE₁(s)*(TE₂(s)*A₂)
          apply Continuous.mul
          · exact continuous_timeEvolutionOp _
          · apply Continuous.mul
            · exact continuous_timeEvolutionOp _
            · exact continuous_const
  have h_int : IntervalIntegrable (interpolationDerivativeOp H₁ H₂ t) MeasureTheory.volume 0 t :=
    h_cont.intervalIntegrable 0 t
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  -- h_ftc : ∫₀ᵗ F' = F(t) - F(0).  We need F(0) - F(t).
  -- F(0) - F(t) = -(F(t) - F(0)) = -(∫F')
  -- So opNorm(F(0)-F(t)) = opNorm(∫F') (by opNorm_neg)
  refine ⟨?endpointBound⟩
  have h_neg : interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t
      = -(interpolationOp H₁ H₂ t t - interpolationOp H₁ H₂ t 0) := by
    rw [neg_sub]
  rw [h_neg, ← h_ftc, opNorm_neg]
  unfold commutatorBoundRhs
  open scoped Matrix.Norms.L2Operator in
  have h_norm : opNorm (∫ s in (0 : ℝ)..t, interpolationDerivativeOp H₁ H₂ t s)
      ≤ ∫ s in (0 : ℝ)..t, opNorm (interpolationDerivativeOp H₁ H₂ t s) := by
    unfold opNorm
    exact intervalIntegral.norm_integral_le_integral_norm
      (f := interpolationDerivativeOp H₁ H₂ t) ht
  refine le_trans h_norm ?_
  have h_bound : ∀ s ∈ Set.Icc (0 : ℝ) t,
      opNorm (interpolationDerivativeOp H₁ H₂ t s)
      ≤ s * opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
    intro s hs
    exact norm_interpolationDerivativeOp_le H₁ H₂ t s hs.1
  -- Final assembly: same ∫₀ᵗ f ≤ ∫₀ᵗ g pattern as G_diff_norm_bound (line 874)
  let c := opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆)
  have h_int_s_mul_c : IntervalIntegrable (fun s : ℝ => s * c) MeasureTheory.volume (0 : ℝ) t :=
    (Continuous.mul continuous_id continuous_const).intervalIntegrable 0 t
  have h_int_bound : (∫ s in (0 : ℝ)..t, opNorm (interpolationDerivativeOp H₁ H₂ t s))
      ≤ (∫ s in (0 : ℝ)..t, s * c) := by
    refine intervalIntegral.integral_mono_on ht ?_ ?_ ?_
    · exact (h_cont.norm.intervalIntegrable 0 t)
    · exact h_int_s_mul_c
    · intro s hs
      rcases hs with ⟨hs_left, hs_right⟩
      simpa [c] using h_bound s ⟨hs_left, hs_right⟩
  refine le_trans h_int_bound ?_
  -- Compute ∫₀ᵗ s*c ds = c * (t²/2) = (t²/2) * c
  calc
    (∫ s in (0 : ℝ)..t, s * c) = c * (∫ s in (0 : ℝ)..t, s) := by
      rw [intervalIntegral.integral_mul_const, mul_comm]
    _ = c * (((t : ℝ) ^ 2) / 2) := by
      have h_int_x : (∫ s in (0 : ℝ)..t, s) = ((t : ℝ) ^ 2) / 2 := by
        rw [integral_id (a := (0 : ℝ)) (b := t)]
        simp [sq, sub_zero]
      rw [h_int_x]
    _ = (t ^ 2 / 2) * c := by ring
    _ ≤ (t ^ 2 / 2) * opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
      dsimp [c]; rfl

/-- Unconditional one-step commutator error bound for nonnegative time.

The endpoint estimate is derived internally by integration; only Hermiticity
and nonnegative time are required [Lin22, trotter.tex:108-115]. -/
public theorem oneStep_error_bound {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) (ht : 0 ≤ t) :
    opNorm (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
      - firstOrderTrotterStepOp (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t)
      ≤ commutatorBoundRhs H₁ H₂ t :=
  bound_of_duhamelEndpointEstimate H₁ H₂ t (duhamelEndpointEstimate_proof H₁ H₂ t ht) ht

/-! ### Repeated-step error bound via telescoping

Given the one-step bound `‖e^{-iδ(A+B)} - e^{-iδA}e^{-iδB}‖ ≤ (δ²/2)·‖[A,B]‖`,
the standard telescoping identity `Uʳ - Vʳ = Σⱼ U^{r-1-j}(U-V)Vʲ` with
unitary U, V lifts the error to `r` repeated steps. -/

lemma repeated_error_bound {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : r ≠ 0) :
    opNorm
        (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
          - firstOrderTrotterProductOp
              (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r)
      ≤ (t ^ 2 / (2 * (r : ℝ))) * opNorm
          (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  let H₁' := (H₁ : HilbertOperator R)
  let H₂' := (H₂ : HilbertOperator R)
  let δ := t / (r : ℝ)
  have hδ_nonneg : 0 ≤ δ := div_nonneg ht (Nat.cast_nonneg _)
  -- U = TE(A+B, δ), V = TE(A, δ) * TE(B, δ) (one-step Trotter)
  let U := timeEvolutionOp (H₁' + H₂') δ
  let V := firstOrderTrotterStepOp H₁' H₂' δ
  have hU_unitary : U ∈ Matrix.unitaryGroup R.Index ℂ :=
    timeEvolutionOp_mem_unitaryGroup (H₁.2.add H₂.2) δ
  have hV_unitary : V ∈ Matrix.unitaryGroup R.Index ℂ :=
    firstOrderTrotterStepOp_mem_unitaryGroup H₁ H₂ δ
  -- One-step bound: ‖U - V‖ ≤ (δ²/2)·‖[A,B]‖
  have h_one_step : opNorm (U - V) ≤ commutatorBoundRhs H₁ H₂ δ :=
    oneStep_error_bound H₁ H₂ δ hδ_nonneg
  -- Telescoping: ‖U^r - V^r‖ ≤ r·‖U - V‖
  have h_telescope : opNorm (U ^ r - V ^ r) ≤ (r : ℝ) * opNorm (U - V) :=
    HilbertOperator.opNorm_pow_sub_pow_le hU_unitary hV_unitary r
  -- U^r = TE(A+B, t) by timeEvolutionOp_pow_div
  have h_pow : U ^ r = timeEvolutionOp (H₁' + H₂') t := by
    calc
      U ^ r = (timeEvolutionOp (H₁' + H₂') (t / (r : ℝ))) ^ r := rfl
      _ = timeEvolutionOp (H₁' + H₂') t :=
        timeEvolutionOp_pow_div (H₁' + H₂') hr t
  -- V^r = firstOrderTrotterProductOp (by definition)
  have h_prod : V ^ r = firstOrderTrotterProductOp H₁' H₂' t r := by
    calc
      V ^ r = (firstOrderTrotterStepOp H₁' H₂' (t / (r : ℝ))) ^ r := rfl
      _ = firstOrderTrotterProductOp H₁' H₂' t r := rfl
  rw [← h_pow, ← h_prod]
  -- Chain: ‖Uʳ-Vʳ‖ ≤ r·‖U-V‖ ≤ r·(δ²/2)·‖[A,B]‖ = (t²/(2r))·‖[A,B]‖
  refine le_trans h_telescope ?_
  refine le_trans (mul_le_mul_of_nonneg_left h_one_step (Nat.cast_nonneg _)) ?_
  unfold commutatorBoundRhs
  have h_scalar_eq : (r : ℝ) * ((δ ^ 2 / 2) *
      opNorm (⁅H₁', H₂'⁆))
      = (t ^ 2 / (2 * (r : ℝ))) *
        opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
    calc
      (r : ℝ) * ((δ ^ 2 / 2) *
          opNorm (⁅H₁', H₂'⁆))
          = ((r : ℝ) * (δ ^ 2 / 2)) *
            opNorm (⁅H₁', H₂'⁆) := by ring
      _ = (t ^ 2 / (2 * (r : ℝ))) *
          opNorm (⁅H₁', H₂'⁆) := by
        dsimp [δ]
        field_simp [show (r : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hr]
      _ = (t ^ 2 / (2 * (r : ℝ))) *
          opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
        simp [H₁', H₂']
  exact h_scalar_eq.le

end TrotterOneStepErrorBound

namespace Trotter

/-- The first-order product with the largest index on the left
[CST+21, prelim.tex:30-35]. -/
def firstOrderStep {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) : UnitaryOperator R :=
  finiteFirstOrderTrotterStep (fun j : Fin L => H j.rev) t

/-- The exact tail-commutator quantity in the first-order bound
[CST+21, prefactor.tex:45-50]. -/
def firstOrderCommutatorSum {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) : ℝ :=
  ∑ j : Fin L, opNorm
    (⁅(∑ k : Fin L, if j < k then (H k : HilbertOperator R) else 0),
      (H j : HilbertOperator R)⁆)

/-- Reversing the family converts the ascending product to the descending product. -/
lemma firstOrderStep_eq_reverse {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) :
    firstOrderStep H t = finiteFirstOrderTrotterStep (fun j : Fin L => H j.rev) t :=
  rfl

/-- Raw ordered product formula for the certified step. -/
lemma coe_firstOrderStep {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) :
    (firstOrderStep H t : HilbertOperator R) =
      (List.ofFn fun j : Fin L => timeEvolutionOp (H j.rev : HilbertOperator R) t).prod := by
  simp [firstOrderStep]

@[simp]
lemma firstOrderStep_empty {R : Register} (H : HamiltonianFamily R 0) (t : ℝ) :
    firstOrderStep H t = 1 := by
  simp [firstOrderStep, finiteFirstOrderTrotterStep]

/-- The head is the rightmost factor of the descending product. -/
lemma firstOrderStep_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) (t : ℝ) :
    firstOrderStep H t =
      firstOrderStep (fun j : Fin L => H j.succ) t * timeEvolution (H 0) t := by
  unfold firstOrderStep finiteFirstOrderTrotterStep
  rw [List.ofFn_succ']
  simp only [Fin.rev_castSucc, Fin.rev_last, List.prod_concat]

@[simp]
lemma firstOrderStep_singleton {R : Register} (H : HamiltonianFamily R 1) (t : ℝ) :
    firstOrderStep H t = timeEvolution (H 0) t := by
  rw [firstOrderStep_succ]
  simp

/-- Two entries occur in descending order. -/
lemma firstOrderStep_pair {R : Register} (H₀ H₁ : Hamiltonian R) (t : ℝ) :
    firstOrderStep ![H₀, H₁] t = timeEvolution H₁ t * timeEvolution H₀ t := by
  rw [firstOrderStep_succ, firstOrderStep_singleton]
  rfl

lemma firstOrderCommutatorSum_nonneg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) : 0 ≤ firstOrderCommutatorSum H :=
  Finset.sum_nonneg fun _ _ => opNorm_nonneg _

@[simp]
lemma firstOrderCommutatorSum_empty {R : Register} (H : HamiltonianFamily R 0) :
    firstOrderCommutatorSum H = 0 := by
  simp [firstOrderCommutatorSum]

/-- Splitting off the head retains the sum inside its commutator. -/
lemma firstOrderCommutatorSum_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) :
    firstOrderCommutatorSum H =
      opNorm (⁅(Hamiltonian.sum (fun j : Fin L => H j.succ) : HilbertOperator R),
        (H 0 : HilbertOperator R)⁆) +
      firstOrderCommutatorSum (fun j : Fin L => H j.succ) := by
  classical
  unfold firstOrderCommutatorSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.lt_irrefl, ↓reduceIte, Fin.succ_pos,
    Fin.not_lt_zero, Fin.succ_lt_succ_iff, zero_add, Hamiltonian.coe_sum]

@[simp]
lemma firstOrderCommutatorSum_singleton {R : Register} (H : HamiltonianFamily R 1) :
    firstOrderCommutatorSum H = 0 := by
  simp [firstOrderCommutatorSum_succ, Hamiltonian.coe_sum, Ring.lie_def]

/-- The two-entry quantity uses the same commutator as the two-term bound. -/
lemma firstOrderCommutatorSum_pair {R : Register} (H₀ H₁ : Hamiltonian R) :
    firstOrderCommutatorSum ![H₀, H₁] =
      opNorm (⁅(H₁ : HilbertOperator R), (H₀ : HilbertOperator R)⁆) := by
  simp [firstOrderCommutatorSum_succ, Hamiltonian.coe_sum, Ring.lie_def]

private lemma hamiltonian_sum_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) :
    Hamiltonian.sum H = Hamiltonian.sum (fun j : Fin L => H j.succ) + H 0 := by
  apply Subtype.ext
  simp [Hamiltonian.coe_sum, Fin.sum_univ_succ, add_comm]

private lemma hamiltonian_sum_empty {R : Register} (H : HamiltonianFamily R 0) :
    Hamiltonian.sum H = 0 := by
  apply Subtype.ext
  simp

private lemma timeEvolution_neg_neg {R : Register} (H : Hamiltonian R) (t : ℝ) :
    timeEvolution (-H) (-t) = timeEvolution H t := by
  apply Subtype.ext
  simp [timeEvolutionOp]

private lemma firstOrderStep_neg_neg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) :
    firstOrderStep (fun j => -H j) (-t) = firstOrderStep H t := by
  simp [firstOrderStep, finiteFirstOrderTrotterStep, timeEvolution_neg_neg]

private lemma hamiltonian_sum_neg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) :
    Hamiltonian.sum (fun j => -H j) = -(Hamiltonian.sum H) := by
  apply Subtype.ext
  simp

private lemma firstOrderCommutatorSum_neg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) :
    firstOrderCommutatorSum (fun j => -H j) = firstOrderCommutatorSum H := by
  classical
  unfold firstOrderCommutatorSum
  apply Finset.sum_congr rfl
  intro j _
  have hsum : (∑ k : Fin L, if j < k then ((-H k : Hamiltonian R) : HilbertOperator R)
      else 0) = -(∑ k : Fin L, if j < k then (H k : HilbertOperator R) else 0) := by
    simp only [Hamiltonian.coe_neg, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [hsum, Hamiltonian.coe_neg]
  simp [Ring.lie_def]

private lemma firstOrder_error_bound_nonneg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) (ht : 0 ≤ t) :
    opNorm ((firstOrderStep H t : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 2 / 2) * firstOrderCommutatorSum H := by
  induction L with
  | zero =>
    simp [hamiltonian_sum_empty, timeEvolutionOp]
  | succ L ih =>
    let T : HamiltonianFamily R L := fun j => H j.succ
    let S := Hamiltonian.sum T
    let P : HilbertOperator R := firstOrderStep T t
    let V : HilbertOperator R := timeEvolution S t
    let U : HilbertOperator R := timeEvolution (H 0) t
    have hsum : Hamiltonian.sum H = S + H 0 := hamiltonian_sum_succ H
    have htail : opNorm (P - V) ≤ (t ^ 2 / 2) * firstOrderCommutatorSum T := ih T
    have hpair : opNorm (V * U -
        (timeEvolution (S + H 0) t : HilbertOperator R)) ≤
        (t ^ 2 / 2) * opNorm (⁅(S : HilbertOperator R), (H 0 : HilbertOperator R)⁆) := by
      rw [opNorm_sub_comm]
      exact TrotterOneStepErrorBound.oneStep_error_bound S (H 0) t ht
    have hcancel : opNorm (P * U - V * U) = opNorm (P - V) := by
      rw [← sub_mul]
      exact opNorm_mul_unitaryGroup (P - V) (timeEvolutionOp_mem_unitaryGroup (H 0).2 t)
    rw [firstOrderStep_succ, hsum]
    change opNorm (P * U - (timeEvolution (S + H 0) t : HilbertOperator R)) ≤ _
    calc
      _ ≤ opNorm (P * U - V * U) +
          opNorm (V * U - (timeEvolution (S + H 0) t : HilbertOperator R)) :=
        opNorm_sub_le_add _ (V * U) _
      _ ≤ (t ^ 2 / 2) * firstOrderCommutatorSum T +
          (t ^ 2 / 2) * opNorm (⁅(S : HilbertOperator R), (H 0 : HilbertOperator R)⁆) := by
        rw [hcancel]
        exact add_le_add htail hpair
      _ = (t ^ 2 / 2) * firstOrderCommutatorSum H := by
        rw [firstOrderCommutatorSum_succ]
        dsimp [S, T]
        ring

/-- Finite-family first-order error with the exact tail-commutator prefactor.

The nonnegative-time estimate is [CST+21, prefactor.tex:45-50], with descending
order [CST+21, prelim.tex:30-35]. Simultaneous negation of the family and time
extends it to every real time without reversing the factors. -/
public theorem firstOrder_error_bound {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) :
    opNorm ((firstOrderStep H t : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 2 / 2) * firstOrderCommutatorSum H := by
  by_cases ht : 0 ≤ t
  · exact firstOrder_error_bound_nonneg H t ht
  · have h := firstOrder_error_bound_nonneg (fun j => -H j) (-t) (by linarith)
    simpa only [firstOrderStep_neg_neg, hamiltonian_sum_neg, timeEvolution_neg_neg,
      neg_sq, firstOrderCommutatorSum_neg] using h

/-- Unitary telescoping lifts the finite-family first-order estimate to positive
step counts, for every real time. The one-step prefactor is from
[CST+21, prefactor.tex:45-50]. -/
lemma firstOrder_repeated_error_bound {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) (r : ℕ) (hr : 0 < r) :
    opNorm (((firstOrderStep H (t / (r : ℝ))) ^ r : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 2 / (2 * (r : ℝ))) * firstOrderCommutatorSum H := by
  let P := firstOrderStep H (t / (r : ℝ))
  let U := timeEvolution (Hamiltonian.sum H) (t / (r : ℝ))
  have htel := opNorm_pow_sub_pow_le P.property U.property r
  have hpow : (U : HilbertOperator R) ^ r =
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R) :=
    timeEvolutionOp_pow_div _ (Nat.ne_zero_of_lt hr) t
  have hstep := firstOrder_error_bound H (t / (r : ℝ))
  have hscalar : (r : ℝ) * (((t / (r : ℝ)) ^ 2 / 2) * firstOrderCommutatorSum H) =
      (t ^ 2 / (2 * (r : ℝ))) * firstOrderCommutatorSum H := by
    field_simp [show (r : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hr)]
  calc
    _ = opNorm ((P : HilbertOperator R) ^ r - (U : HilbertOperator R) ^ r) := by
      rw [hpow]
    _ ≤ (r : ℝ) * opNorm ((P : HilbertOperator R) - (U : HilbertOperator R)) := htel
    _ ≤ (r : ℝ) * (((t / (r : ℝ)) ^ 2 / 2) * firstOrderCommutatorSum H) :=
      mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
    _ = _ := hscalar

/-- Specializing to `[H₂, H₁]` recovers the original raw two-term step. -/
lemma firstOrderStep_pair_eq_twoTerm {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    (firstOrderStep ![H₂, H₁] t : HilbertOperator R) =
      firstOrderTrotterStepOp (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t := by
  rw [firstOrderStep_pair]
  rfl

/-- The reversed two-entry family has the original total Hamiltonian. -/
lemma firstOrder_sum_pair {R : Register} (H₁ H₂ : Hamiltonian R) :
    Hamiltonian.sum ![H₂, H₁] = H₁ + H₂ := by
  apply Subtype.ext
  simp [Hamiltonian.coe_sum, Fin.sum_univ_succ, add_comm]

/-- Recovery of the original two-term one-step formula by finite-family specialization. -/
lemma firstOrder_twoTerm_error_bound {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) (_ht : 0 ≤ t) :
    opNorm (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t -
      firstOrderTrotterStepOp (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t) ≤
      TrotterOneStepErrorBound.commutatorBoundRhs H₁ H₂ t := by
  have h := firstOrder_error_bound ![H₂, H₁] t
  rw [firstOrderStep_pair_eq_twoTerm, firstOrder_sum_pair, firstOrderCommutatorSum_pair,
    opNorm_sub_comm] at h
  exact h

/-- Recovery of the original repeated two-term formula by finite-family specialization. -/
lemma firstOrder_twoTerm_repeated_error_bound {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) (_ht : 0 ≤ t) (r : ℕ) (hr : r ≠ 0) :
    opNorm (timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t -
      firstOrderTrotterProductOp (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r) ≤
      (t ^ 2 / (2 * (r : ℝ))) *
        opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  have h := firstOrder_repeated_error_bound ![H₂, H₁] t r (Nat.pos_of_ne_zero hr)
  simp only [firstOrderStep_pair_eq_twoTerm, firstOrder_sum_pair,
    firstOrderCommutatorSum_pair] at h
  rw [opNorm_sub_comm] at h
  exact h

end Trotter

end

end QuantumAlg
