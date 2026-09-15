/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Noncommutative
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Core.Base.Hamiltonian
public import QuantumAlg.Components.Oracle.TimeEvolution
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Hamiltonian evolution and first-order product formulas

Time-independent evolution is the matrix exponential `exp (-i t H)`
[Lin22, trotter.tex:3]. The first-order product formula replaces evolution
under a sum by repeated products of individual evolutions
[Lin22, trotter.tex:20-28].

The exact commuting case covers both two summands and finite ordered families
[CMN+18, simalg.tex:21; pfappendix.tex:191].
The noncommuting two-term estimate is proved by differentiating an interpolation,
applying the fundamental theorem of calculus, and integrating the commutator
bound. For nonnegative time the one-step constant is `t² / 2`, and telescoping
unitary products gives `t² / (2r)` after `r > 0` steps. These are operator
identities and norm estimates; no implemented circuit or resource claim is made.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator

noncomputable section

theorem hasDerivAt_timeEvolutionOp {R : Register} (H : HilbertOperator R) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp H u)
      (timeEvolutionOp H t * ((-Complex.I) • H)) t := by
  let A : HilbertOperator R := (-Complex.I) • H
  have hderiv :
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
        (NormedSpace.exp (t • A) * A) t := by
    open scoped Matrix.Norms.L2Operator in
    exact hasDerivAt_exp_smul_const A t
  convert hderiv using 1
  · funext u
    have harg : (-(Complex.I * (u : ℂ))) • H = u • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]
  · have harg : (-(Complex.I * (t : ℂ))) • H = t • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]

theorem hasDerivAt_timeEvolutionOp' {R : Register} (H : HilbertOperator R) (t : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp H u)
      (((-Complex.I) • H) * timeEvolutionOp H t) t := by
  let A : HilbertOperator R := (-Complex.I) • H
  have hderiv :
      HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A))
        (A * NormedSpace.exp (t • A)) t := by
    open scoped Matrix.Norms.L2Operator in
    exact hasDerivAt_exp_smul_const' A t
  convert hderiv using 1
  · funext u
    have harg : (-(Complex.I * (u : ℂ))) • H = u • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]
  · have harg : (-(Complex.I * (t : ℂ))) • H = t • A := by
      ext i j
      simp [A]
      ring_nf
    rw [timeEvolutionOp, harg]

theorem opNorm_timeEvolutionOp {R : Register} [Nonempty R.Index]
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ) :
    opNorm (timeEvolutionOp H t) = 1 :=
  opNorm_of_mem_unitaryGroup (timeEvolutionOp_mem_unitaryGroup hH t)

theorem opNorm_timeEvolutionOp_mul {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ)
    (A : HilbertOperator R) :
    opNorm (timeEvolutionOp H t * A) = opNorm A :=
  opNorm_unitaryGroup_mul A (timeEvolutionOp_mem_unitaryGroup hH t)

theorem opNorm_mul_timeEvolutionOp {R : Register}
    {H : HilbertOperator R} (hH : H.IsHermitian) (t : ℝ)
    (A : HilbertOperator R) :
    opNorm (A * timeEvolutionOp H t) = opNorm A :=
  opNorm_mul_unitaryGroup A (timeEvolutionOp_mem_unitaryGroup hH t)

/-- A finite ordered family of Hamiltonian terms on a common register. -/
abbrev HamiltonianFamily (R : Register) (L : ℕ) : Type :=
  Fin L → Hamiltonian R

/-- The Hamiltonian obtained by summing a finite ordered family. -/
def hamiltonianSum {R : Register} {L : ℕ} (terms : HamiltonianFamily R L) :
    Hamiltonian R :=
  ⟨∑ j : Fin L, (terms j : HilbertOperator R), by
    classical
    induction (Finset.univ : Finset (Fin L)) using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (terms a).2.add ih⟩

@[simp]
theorem coe_hamiltonianSum {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) :
    ((hamiltonianSum terms : Hamiltonian R) : HilbertOperator R) =
      ∑ j : Fin L, (terms j : HilbertOperator R) := rfl

/-- Pairwise commutation of all Hamiltonian terms in a finite family. -/
def PairwiseCommute {R : Register} {L : ℕ} (terms : HamiltonianFamily R L) : Prop :=
  ∀ i j : Fin L, Commute (terms i : HilbertOperator R) (terms j : HilbertOperator R)

/-- One first-order product step, with its unconditional unitarity in the carrier. -/
def finiteFirstOrderTrotterStep {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (dt : ℝ) : UnitaryOperator R :=
  (List.ofFn fun j : Fin L => timeEvolution (terms j) dt).prod

@[simp]
theorem coe_finiteFirstOrderTrotterStep {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (dt : ℝ) :
    ((finiteFirstOrderTrotterStep terms dt : UnitaryOperator R) : HilbertOperator R) =
      (List.ofFn fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) dt).prod := by
  simp [finiteFirstOrderTrotterStep, List.map_ofFn, Function.comp_def]

/-- Repeated finite-family product evolution as a certified unitary operator. -/
def finiteFirstOrderTrotterProduct {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (t : ℝ) (r : ℕ) : UnitaryOperator R :=
  (finiteFirstOrderTrotterStep terms (t / (r : ℝ))) ^ r

@[simp]
theorem coe_finiteFirstOrderTrotterProduct {R : Register} {L : ℕ}
    (terms : HamiltonianFamily R L) (t : ℝ) (r : ℕ) :
    ((finiteFirstOrderTrotterProduct terms t r : UnitaryOperator R) : HilbertOperator R) =
      ((finiteFirstOrderTrotterStep terms (t / (r : ℝ)) : UnitaryOperator R) :
        HilbertOperator R) ^ r := by
  simp [finiteFirstOrderTrotterProduct]

/-- Exact one-step finite-family first-order product formula for pairwise
commuting Hamiltonian terms. -/
theorem timeEvolution_eq_finiteTrotterStep_of_pairwise_commute
    {R : Register} {L : ℕ} (terms : HamiltonianFamily R L)
    (hcomm : PairwiseCommute terms) (t : ℝ) :
    timeEvolution (hamiltonianSum terms) t = finiteFirstOrderTrotterStep terms t := by
  apply Subtype.ext
  change timeEvolutionOp (hamiltonianSum terms : HilbertOperator R) t =
    ((finiteFirstOrderTrotterStep terms t : UnitaryOperator R) : HilbertOperator R)
  classical
  let c : ℂ := -(Complex.I * (t : ℂ))
  have hscaled : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun Commute fun j : Fin L => c • (terms j : HilbertOperator R)) := by
    intro i _ j _ _
    exact (hcomm i j).smul_left c |>.smul_right c
  have hstepCommUniv : ((Finset.univ : Finset (Fin L)) : Set (Fin L)).Pairwise
      (Function.onFun Commute fun j : Fin L =>
        timeEvolutionOp (terms j : HilbertOperator R) t) := by
    intro i _ j _ _
    exact ((hcomm i j).smul_left c |>.smul_right c).exp
  rw [timeEvolutionOp, coe_hamiltonianSum, coe_finiteFirstOrderTrotterStep]
  change NormedSpace.exp (c • ∑ j : Fin L, (terms j : HilbertOperator R))
    = (List.ofFn fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) t).prod
  rw [Finset.smul_sum]
  rw [Matrix.exp_sum_of_commute Finset.univ
    (fun j : Fin L => c • (terms j : HilbertOperator R)) hscaled]
  have hstepCommRange :
      (((List.finRange L).toFinset : Finset (Fin L)) : Set (Fin L)).Pairwise
        (Function.onFun Commute fun j : Fin L =>
          timeEvolutionOp (terms j : HilbertOperator R) t) := by
    simpa [List.toFinset_finRange] using hstepCommUniv
  have hnoncomm := Finset.noncommProd_toFinset (List.finRange L)
      (fun j : Fin L => timeEvolutionOp (terms j : HilbertOperator R) t)
      hstepCommRange
      (List.nodup_finRange L)
  simpa [timeEvolutionOp, c, List.ofFn_eq_map,
    List.toFinset_finRange] using hnoncomm

/-- One first-order Trotter step for two Hamiltonian summands, at the raw
operator level. -/
def firstOrderTrotterStepOp {R : Register} (H₁ H₂ : HilbertOperator R) (dt : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp H₁ dt * timeEvolutionOp H₂ dt

/-- A two-term first-order Trotter step is unitary when both summands are Hamiltonians. -/
theorem firstOrderTrotterStepOp_mem_unitaryGroup {R : Register}
    (H₁ H₂ : Hamiltonian R) (dt : ℝ) :
    firstOrderTrotterStepOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) dt
      ∈ Matrix.unitaryGroup R.Index ℂ := by
  unfold firstOrderTrotterStepOp
  exact mul_mem (timeEvolutionOp_mem_unitaryGroup H₁.2 dt)
    (timeEvolutionOp_mem_unitaryGroup H₂.2 dt)

/-- The repeated first-order Trotter product for two Hamiltonian summands. -/
def firstOrderTrotterProductOp {R : Register} (H₁ H₂ : HilbertOperator R)
    (t : ℝ) (r : ℕ) : HilbertOperator R :=
  (firstOrderTrotterStepOp H₁ H₂ (t / (r : ℝ))) ^ r

/-- The raw operator error of the two-term repeated first-order Trotter product. -/
def firstOrderTrotterErrorOp {R : Register} (H₁ H₂ : HilbertOperator R)
    (t : ℝ) (r : ℕ) : HilbertOperator R :=
  timeEvolutionOp (H₁ + H₂) t - firstOrderTrotterProductOp H₁ H₂ t r

/-- Exact one-step product formula for commuting Hamiltonian operators. -/
theorem timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute {R : Register}
    {H₁ H₂ : HilbertOperator R} (hcomm : Commute H₁ H₂) (t : ℝ) :
    timeEvolutionOp (H₁ + H₂) t = firstOrderTrotterStepOp H₁ H₂ t := by
  rw [timeEvolutionOp, firstOrderTrotterStepOp, timeEvolutionOp, timeEvolutionOp, smul_add]
  apply Matrix.exp_add_of_commute
  exact hcomm.smul_left _ |>.smul_right _

/-- Repeating exact evolution for `t / r` exactly recovers evolution for `t`.
This is an algebraic matrix-exponential identity and does not require
Hermitianity. -/
theorem timeEvolutionOp_pow_div {R : Register} (H : HilbertOperator R) {r : ℕ}
    (hr : r ≠ 0) (t : ℝ) :
    (timeEvolutionOp H (t / (r : ℝ))) ^ r = timeEvolutionOp H t := by
  rw [timeEvolutionOp, timeEvolutionOp]
  rw [← Matrix.exp_nsmul r
    ((-(Complex.I * ((t / (r : ℝ) : ℝ) : ℂ))) • H)]
  congr 1
  ext i j
  simp [nsmul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr hr]

/-- Exact repeated finite-family first-order product formula for pairwise
commuting Hamiltonian terms. -/
public theorem timeEvolution_eq_finiteTrotterProduct_of_pairwise_commute
    {R : Register} {L : ℕ} (terms : HamiltonianFamily R L)
    (hcomm : PairwiseCommute terms) {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    timeEvolution (hamiltonianSum terms) t = finiteFirstOrderTrotterProduct terms t r := by
  rw [finiteFirstOrderTrotterProduct]
  rw [← timeEvolution_eq_finiteTrotterStep_of_pairwise_commute terms hcomm (t / (r : ℝ))]
  apply Subtype.ext
  change timeEvolutionOp (hamiltonianSum terms : HilbertOperator R) t =
    (timeEvolutionOp (hamiltonianSum terms : HilbertOperator R) (t / (r : ℝ))) ^ r
  exact (timeEvolutionOp_pow_div (hamiltonianSum terms : HilbertOperator R) hr t).symm

namespace TrotterProductFormula

/-- Exact repeated first-order Trotter product formula for commuting Hamiltonian
summands.  This is the zero-error boundary of the product-formula method; the
noncommuting approximation bound is intentionally not claimed here. -/
theorem commuting_exact {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
      = firstOrderTrotterProductOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r := by
  rw [firstOrderTrotterProductOp]
  rw [← timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute hcomm (t / (r : ℝ))]
  exact (timeEvolutionOp_pow_div
    ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) hr t).symm

/-- The explicit Trotter error operator vanishes for commuting Hamiltonian
summands and nonzero step count. -/
theorem error_eq_zero_of_commute {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    {r : ℕ} (hr : r ≠ 0) (t : ℝ) :
    firstOrderTrotterErrorOp
        (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t r = 0 := by
  rw [firstOrderTrotterErrorOp, commuting_exact H₁ H₂ hcomm hr t, sub_self]

end TrotterProductFormula

namespace TrotterOneStepErrorBound

/-- The sharp two-term one-step commutator bound right-hand side. -/
def commutatorBoundRhs {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) : ℝ :=
  (t ^ 2 / 2) *
    opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆)

theorem commutatorBoundRhs_nonneg {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    0 ≤ commutatorBoundRhs H₁ H₂ t := by
  unfold commutatorBoundRhs
  exact mul_nonneg (div_nonneg (sq_nonneg t) (by norm_num))
    (opNorm_nonneg (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆))

@[simp]
theorem commutatorBoundRhs_eq_zero_of_commute {R : Register}
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

theorem statement_iff_oneStepErrorOp {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
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
private theorem interpolationOp_zero {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    interpolationOp H₁ H₂ t 0
      = timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t := by
  simp [interpolationOp, firstOrderTrotterStepOp, timeEvolutionOp]

@[simp]
private theorem interpolationOp_self {R : Register} (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    interpolationOp H₁ H₂ t t
      = firstOrderTrotterStepOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t := by
  simp [interpolationOp, timeEvolutionOp]

/-- The one-step error is the difference between the interpolation endpoints. -/
private theorem oneStepErrorOp_eq_interpolation_endpoints {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    oneStepErrorOp H₁ H₂ t = interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t := by
  simp [oneStepErrorOp]

/-- Norm form of the interpolation endpoint identity. -/
private theorem opNorm_oneStepErrorOp_eq_interpolation_endpoints {R : Register}
    (H₁ H₂ : Hamiltonian R) (t : ℝ) :
    opNorm (oneStepErrorOp H₁ H₂ t)
      = opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t) := by
  rw [oneStepErrorOp_eq_interpolation_endpoints]

/-- An analytic endpoint estimate for the interpolation implies the target
one-step Trotter bound. -/
private theorem statement_of_interpolation_endpoints_bound {R : Register}
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
private theorem bound_of_duhamelEndpointEstimate {R : Register}
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
theorem opNorm_commutatorKernel {R : Register}
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
theorem opNorm_commutatorKernel_le {R : Register}
    (H₁ H₂ : Hamiltonian R) (t s : ℝ) :
    opNorm (commutatorKernel H₁ H₂ t s)
      ≤ opNorm (⁅(H₁ : HilbertOperator R), (H₂ : HilbertOperator R)⁆) := by
  rw [opNorm_commutatorKernel H₁ H₂ t s]

/-- The commutator kernel vanishes on the commuting boundary. -/
theorem commutatorKernel_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t s : ℝ) :
    commutatorKernel H₁ H₂ t s = 0 := by
  simp [commutatorKernel, hcomm.lie_eq]

@[simp]
theorem opNorm_commutatorKernel_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t s : ℝ) :
    opNorm (commutatorKernel H₁ H₂ t s) = 0 := by
  rw [commutatorKernel_eq_zero_of_commute H₁ H₂ hcomm t s, opNorm_zero]

/-- One-step exactness on the commuting boundary.  The noncommuting
commutator-norm estimate is proved below. -/
theorem commuting_boundary_eq {R : Register} (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    timeEvolutionOp ((H₁ : HilbertOperator R) + (H₂ : HilbertOperator R)) t
      = firstOrderTrotterStepOp
          (H₁ : HilbertOperator R) (H₂ : HilbertOperator R) t :=
  timeEvolutionOp_add_eq_firstOrderTrotterStepOp_of_commute hcomm t

/-- On the commuting boundary, the interpolation endpoints coincide. -/
private theorem interpolation_endpoints_sub_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t = 0 := by
  rw [interpolationOp_zero, interpolationOp_self, commuting_boundary_eq H₁ H₂ hcomm t,
    sub_self]

private theorem opNorm_interpolation_endpoints_eq_zero_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    opNorm (interpolationOp H₁ H₂ t 0 - interpolationOp H₁ H₂ t t) = 0 := by
  rw [interpolation_endpoints_sub_eq_zero_of_commute H₁ H₂ hcomm t, opNorm_zero]

/-- The Duhamel endpoint estimate is witnessed on the commuting boundary. -/
private theorem duhamelEndpointEstimate_of_commute {R : Register}
    (H₁ H₂ : Hamiltonian R)
    (hcomm : Commute (H₁ : HilbertOperator R) (H₂ : HilbertOperator R))
    (t : ℝ) :
    DuhamelEndpointEstimate H₁ H₂ t := by
  refine ⟨?_⟩
  rw [opNorm_interpolation_endpoints_eq_zero_of_commute H₁ H₂ hcomm t]
  exact commutatorBoundRhs_nonneg H₁ H₂ t

/-- The commutator-norm error bound is trivial on the commuting boundary. -/
theorem commuting_boundary_operatorNorm {R : Register} (H₁ H₂ : Hamiltonian R)
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
private theorem duhamelEndpointEstimate_proof {R : Register}
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

/-- Telescoping norm identity for unitary operators:
`‖U^r - V^r‖ ≤ r * ‖U - V‖` when U, V are unitaries. -/
private lemma norm_pow_sub_pow_le_unitary {R : Register}
    {U V : HilbertOperator R}
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ)
    (hV : V ∈ Matrix.unitaryGroup R.Index ℂ)
    (r : ℕ) :
    opNorm (U ^ r - V ^ r) ≤ (r : ℝ) * opNorm (U - V) := by
  induction r
  case zero =>
    rw [pow_zero, pow_zero, sub_self, opNorm_zero (R := R)]
    simp
  case succ k ih =>
    rw [pow_succ_sub_pow_succ_eq U V k]
    -- Triangle inequality
    have h_tri := opNorm_add_le (U * (U ^ k - V ^ k)) ((U - V) * (V ^ k))
    -- Submultiplicative + unitary norm bounds
    have h_sub : opNorm (U * (U ^ k - V ^ k)) +
        opNorm ((U - V) * (V ^ k))
        ≤ opNorm (U ^ k - V ^ k) + opNorm (U - V) := by
      rw [opNorm_unitaryGroup_mul (U ^ k - V ^ k) hU,
        opNorm_mul_unitaryGroup (U - V) (pow_mem hV k)]
    refine le_trans h_tri (le_trans h_sub ?_)
    -- Induction: ‖Uᵏ-Vᵏ‖ ≤ k·‖U-V‖ ⇒ ‖Uᵏ-Vᵏ‖ + ‖U-V‖ ≤ (k+1)·‖U-V‖
    have h_arith : opNorm (U ^ k - V ^ k) + opNorm (U - V)
        ≤ ((k : ℕ).succ : ℝ) * opNorm (U - V) := by
      calc
        opNorm (U ^ k - V ^ k) + opNorm (U - V)
            ≤ (k : ℝ) * opNorm (U - V) + opNorm (U - V) :=
          (add_le_add_iff_right (opNorm (U - V))).mpr ih
        _ = ((k : ℕ).succ : ℝ) * opNorm (U - V) := by push_cast; ring
    exact h_arith

theorem repeated_error_bound {R : Register}
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
    norm_pow_sub_pow_le_unitary hU_unitary hV_unitary r
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

end

end QuantumAlg
