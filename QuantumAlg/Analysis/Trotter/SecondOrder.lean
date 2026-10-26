/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.Trotter.FirstOrder

/-!
# Second-order product-formula error

The symmetric product and its nested-commutator prefactors follow
[CST+21, prefactor.tex:52-113], using the product convention in
[CST+21, prelim.tex:30-35]. All evolution operators are intrinsically unitary.
-/

@[expose] public section

namespace QuantumAlg

open HilbertOperator TrotterOneStepErrorBound

noncomputable section

namespace Trotter

/-- The ascending half-time product followed by the descending half-time product. -/
def secondOrderStep {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) : UnitaryOperator R :=
  finiteFirstOrderTrotterStep H (t / 2) * firstOrderStep H (t / 2)

/-- Nested tail commutators with the normalization of [CST+21, prefactor.tex:105-114]. -/
def secondOrderCommutatorSum {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) : ℝ :=
  (∑ j : Fin L, opNorm (⁅(∑ k : Fin L, if j < k then
    (H k : HilbertOperator R) else 0), ⁅(∑ k : Fin L, if j < k then
    (H k : HilbertOperator R) else 0), (H j : HilbertOperator R)⁆⁆)) +
  (1 / 2 : ℝ) * ∑ j : Fin L, opNorm (⁅(H j : HilbertOperator R),
    ⁅(H j : HilbertOperator R), (∑ k : Fin L, if j < k then
      (H k : HilbertOperator R) else 0)⁆⁆)

/-- The weighted nested-commutator quantity is nonnegative. -/
lemma secondOrderCommutatorSum_nonneg {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) : 0 ≤ secondOrderCommutatorSum H := by
  unfold secondOrderCommutatorSum
  exact add_nonneg (Finset.sum_nonneg fun _ _ => opNorm_nonneg _)
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => opNorm_nonneg _))

@[simp]
lemma secondOrderStep_empty {R : Register} (H : HamiltonianFamily R 0) (t : ℝ) :
    secondOrderStep H t = 1 := by
  simp [secondOrderStep, finiteFirstOrderTrotterStep]

/-- Splitting the outermost pair of half-time factors. -/
lemma secondOrderStep_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) (t : ℝ) :
    secondOrderStep H t = timeEvolution (H 0) (t / 2) *
      secondOrderStep (fun j : Fin L => H j.succ) t * timeEvolution (H 0) (t / 2) := by
  simp only [secondOrderStep, firstOrderStep_succ]
  unfold finiteFirstOrderTrotterStep
  rw [List.ofFn_succ]
  simp [mul_assoc]

@[simp]
lemma secondOrderStep_singleton {R : Register} (H : HamiltonianFamily R 1) (t : ℝ) :
    secondOrderStep H t = timeEvolution (H 0) t := by
  rw [secondOrderStep_succ, secondOrderStep_empty, mul_one, ← timeEvolution_add]
  congr 1
  ring

/-- Two entries give the standard Strang sandwich. -/
lemma secondOrderStep_pair {R : Register} (A B : Hamiltonian R) (t : ℝ) :
    secondOrderStep ![A, B] t =
      timeEvolution A (t / 2) * timeEvolution B t * timeEvolution A (t / 2) := by
  rw [secondOrderStep_succ, secondOrderStep_singleton]
  rfl

@[simp]
lemma secondOrderCommutatorSum_empty {R : Register} (H : HamiltonianFamily R 0) :
    secondOrderCommutatorSum H = 0 := by
  simp [secondOrderCommutatorSum]

/-- The head contributes the two nested commutators of the tail sum. -/
lemma secondOrderCommutatorSum_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) :
    secondOrderCommutatorSum H =
      opNorm (⁅(Hamiltonian.sum (fun j : Fin L => H j.succ) : HilbertOperator R),
        ⁅(Hamiltonian.sum (fun j : Fin L => H j.succ) : HilbertOperator R),
          (H 0 : HilbertOperator R)⁆⁆) +
      (1 / 2 : ℝ) * opNorm (⁅(H 0 : HilbertOperator R), ⁅(H 0 : HilbertOperator R),
        (Hamiltonian.sum (fun j : Fin L => H j.succ) : HilbertOperator R)⁆⁆) +
      secondOrderCommutatorSum (fun j : Fin L => H j.succ) := by
  classical
  unfold secondOrderCommutatorSum
  simp only [Fin.sum_univ_succ, ↓reduceIte, Fin.succ_pos,
    Fin.not_lt_zero, Fin.succ_lt_succ_iff, zero_add, Hamiltonian.coe_sum]
  ring

private lemma endpoint_bound {R : Register} (f f' : ℝ → HilbertOperator R)
    (b : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ s, HasDerivAt f (f' s) s) (hc : Continuous f') (hb : Continuous b)
    (hn : ∀ s ∈ Set.Icc 0 t, opNorm (f' s) ≤ b s) :
    opNorm (f t - f 0) ≤ ∫ s in (0 : ℝ)..t, b s := by
  open scoped Matrix.Norms.L2Operator in
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable 0 t)]
  exact (intervalIntegral.norm_integral_le_integral_norm ht).trans
    (intervalIntegral.integral_mono_on ht (hc.norm.intervalIntegrable 0 t)
      (hb.intervalIntegrable 0 t) hn)

private def conjugationRemainder {R : Register} (H X : HilbertOperator R) (s : ℝ) :
    HilbertOperator R :=
  gFunc H X s - gFunc H X 0 - s • gDeriv H X 0

private lemma conjugationRemainder_bound {R : Register}
    (H X : HilbertOperator R) (hH : H.IsHermitian) (s : ℝ) (hs : 0 ≤ s) :
    opNorm (conjugationRemainder H X s) ≤ (s ^ 2 / 2) * opNorm (⁅H, ⁅H, X⁆⁆) := by
  have hd : ∀ u, HasDerivAt (conjugationRemainder H X)
      (gDeriv H X u - gDeriv H X 0) u := by
    intro u
    open scoped Matrix.Norms.L2Operator in
    convert
      ((hasDerivAt_gFunc H X u).sub_const (gFunc H X 0)).sub
        ((hasDerivAt_id u).smul_const (gDeriv H X 0)) using 1
    all_goals first | rfl | simp
  have hn : ∀ u ∈ Set.Icc 0 s,
      opNorm (gDeriv H X u - gDeriv H X 0) ≤ u * opNorm (⁅H, ⁅H, X⁆⁆) := by
    intro u hu
    have heq : gDeriv H X u - gDeriv H X 0 =
        (-Complex.I) • (gFunc H ⁅H, X⁆ u - gFunc H ⁅H, X⁆ 0) := by
      simp [gDeriv, gFunc, smul_sub]
    rw [heq, opNorm_smul]
    simpa using G_diff_norm_bound H ⁅H, X⁆ hH u hu.1
  have h := endpoint_bound (conjugationRemainder H X)
    (fun u => gDeriv H X u - gDeriv H X 0)
    (fun u => u * opNorm (⁅H, ⁅H, X⁆⁆)) s hs hd
    ((continuous_gDeriv H X).sub continuous_const) (continuous_id.mul continuous_const) hn
  simpa [conjugationRemainder, intervalIntegral.integral_mul_const, integral_id] using h

private def strangDefect {R : Register} (A B : HilbertOperator R) (s : ℝ) :
    HilbertOperator R :=
  gFunc (-A) B (s / 2) - B - (1 / 2 : ℝ) • (gFunc B A s - A)

private lemma strangDefect_remainders {R : Register} (A B : HilbertOperator R) (s : ℝ) :
    strangDefect A B s = conjugationRemainder (-A) B (s / 2) -
      (1 / 2 : ℝ) • conjugationRemainder B A s := by
  have hzero : gDeriv (-A) B 0 = gDeriv B A 0 := by
    simp only [gDeriv, timeEvolutionOp_zero, neg_zero, one_mul, mul_one]
    congr 1
    simp only [Ring.lie_def, neg_mul, mul_neg]
    noncomm_ring
  unfold strangDefect conjugationRemainder
  rw [hzero]
  simp only [gFunc, timeEvolutionOp_zero, neg_zero, one_mul, mul_one]
  module

private lemma strangDefect_bound {R : Register} (A B : Hamiltonian R)
    (s : ℝ) (hs : 0 ≤ s) :
    opNorm (strangDefect (A : HilbertOperator R) (B : HilbertOperator R) s) ≤
      (s ^ 2 / 4) * opNorm (⁅(B : HilbertOperator R),
        ⁅(B : HilbertOperator R), (A : HilbertOperator R)⁆⁆) +
      (s ^ 2 / 8) * opNorm (⁅(A : HilbertOperator R),
        ⁅(A : HilbertOperator R), (B : HilbertOperator R)⁆⁆) := by
  rw [strangDefect_remainders]
  have hA := conjugationRemainder_bound (-(A : HilbertOperator R)) B A.2.neg
    (s / 2) (by positivity)
  have hB := conjugationRemainder_bound (B : HilbertOperator R) A B.2 s hs
  have hneg : ⁅-(A : HilbertOperator R), ⁅-(A : HilbertOperator R),
      (B : HilbertOperator R)⁆⁆ = ⁅(A : HilbertOperator R),
        ⁅(A : HilbertOperator R), (B : HilbertOperator R)⁆⁆ := by
    simp only [Ring.lie_def, neg_mul, mul_neg]
    noncomm_ring
  rw [hneg] at hA
  open scoped Matrix.Norms.L2Operator in
  have htriangle := norm_sub_le
    (conjugationRemainder (-(A : HilbertOperator R)) B (s / 2))
    ((1 / 2 : ℝ) • conjugationRemainder (B : HilbertOperator R) A s)
  open scoped Matrix.Norms.L2Operator in
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    at htriangle
  change opNorm _ ≤ opNorm _ + (1 / 2 : ℝ) * opNorm _ at htriangle
  exact htriangle.trans (by nlinarith [hA, hB])

private def strangInterpolation {R : Register} (A B : HilbertOperator R) (t s : ℝ) :
    HilbertOperator R :=
  timeEvolutionOp (A + B) (t - s) * timeEvolutionOp A (s / 2) *
    timeEvolutionOp B s * timeEvolutionOp A (s / 2)

private def strangDerivative {R : Register} (A B : HilbertOperator R) (t s : ℝ) :
    HilbertOperator R :=
  Complex.I • (timeEvolutionOp (A + B) (t - s) * timeEvolutionOp A (s / 2) *
    strangDefect A B s * timeEvolutionOp B s * timeEvolutionOp A (s / 2))

private lemma timeEvolutionOp_negHamiltonian {R : Register} (A : HilbertOperator R) (s : ℝ) :
    timeEvolutionOp (-A) s = timeEvolutionOp A (-s) := by
  simp [timeEvolutionOp]

private lemma hasDerivAt_strangInterpolation {R : Register}
    (A B : HilbertOperator R) (t s : ℝ) :
    HasDerivAt (strangInterpolation A B t) (strangDerivative A B t s) s := by
  open scoped Matrix.Norms.L2Operator in
  let E := timeEvolutionOp (A + B) (t - s)
  let U := timeEvolutionOp A (s / 2)
  let V := timeEvolutionOp B s
  have hE : HasDerivAt (fun x : ℝ => timeEvolutionOp (A + B) (t - x))
      ((-1 : ℝ) • (E * ((-Complex.I) • (A + B)))) s :=
    (hasDerivAt_timeEvolutionOp (A + B) (t - s)).scomp s
      ((hasDerivAt_id s).const_sub t)
  have hU : HasDerivAt (fun x : ℝ => timeEvolutionOp A (x / 2))
      ((1 / 2 : ℝ) • (((-Complex.I) • A) * U)) s := by
    have hh : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact HasDerivAt.scomp s (hasDerivAt_timeEvolutionOp' A (s / 2)) hh
  have hV := hasDerivAt_timeEvolutionOp' B s
  have hderiv := ((hE.mul hU).mul hV).mul hU
  apply hderiv.congr_deriv
  have hcancelA : U * timeEvolutionOp (-A) (s / 2) = 1 := by
    rw [timeEvolutionOp_negHamiltonian]
    exact timeEvolutionOp_mul_neg A (s / 2)
  have hcancelB : timeEvolutionOp B (-s) * V = 1 := by
    simpa [V] using timeEvolutionOp_mul_neg B (-s)
  have hnegA : timeEvolutionOp (-A) (-(s / 2)) = U := by
    simp [timeEvolutionOp_negHamiltonian, U]
  have hcomm : A * U = U * A := (commute_H_timeEvolutionOp A (s / 2)).eq
  have hleft (X : HilbertOperator R) :
      U * (timeEvolutionOp (-A) (s / 2) * X) = X := by
    rw [← mul_assoc, hcancelA, one_mul]
  have hright (X : HilbertOperator R) : timeEvolutionOp B (-s) * (V * X) = X := by
    rw [← mul_assoc, hcancelB, one_mul]
  have hcomm' (X : HilbertOperator R) : U * (A * X) = A * (U * X) := by
    rw [← mul_assoc, ← hcomm, mul_assoc]
  change (((-1 : ℝ) • (E * ((-Complex.I) • (A + B))) * U +
    E * ((1 / 2 : ℝ) • (((-Complex.I) • A) * U))) * V +
    (E * U) * (((-Complex.I) • B) * V)) * U +
    (E * U * V) * ((1 / 2 : ℝ) • (((-Complex.I) • A) * U)) = _
  change _ = Complex.I • (E * U *
    (timeEvolutionOp (-A) (s / 2) * B * timeEvolutionOp (-A) (-(s / 2)) - B -
      (1 / 2 : ℝ) • (V * A * timeEvolutionOp B (-s) - A)) * V * U)
  rw [hnegA]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, neg_smul, neg_mul, mul_neg, smul_add]
  simp only [mul_assoc, hleft, hright, hcomm']
  module

private lemma continuous_strangDerivative {R : Register}
    (A B : HilbertOperator R) (t : ℝ) : Continuous (strangDerivative A B t) := by
  open scoped Matrix.Norms.L2Operator in
  have hU := (continuous_timeEvolutionOp A).comp (continuous_id.div_const 2)
  have hV := continuous_timeEvolutionOp B
  have hg (H X : HilbertOperator R) : Continuous (gFunc H X) :=
    ((continuous_timeEvolutionOp H).mul continuous_const).mul
      ((continuous_timeEvolutionOp H).comp continuous_neg)
  have hD : Continuous (strangDefect A B) :=
    (((hg (-A) B).comp (continuous_id.div_const 2)).sub continuous_const).sub
      (((hg B A).sub continuous_const).const_smul (1 / 2 : ℝ))
  exact (((((continuous_timeEvolutionOp (A + B)).comp
    (continuous_const.sub continuous_id)).mul hU).mul hD).mul hV |>.mul hU).const_smul
      Complex.I

private lemma strangDerivative_bound {R : Register} (A B : Hamiltonian R)
    (t s : ℝ) (hs : 0 ≤ s) :
    opNorm (strangDerivative (A : HilbertOperator R) (B : HilbertOperator R) t s) ≤
      (s ^ 2 / 4) * opNorm (⁅(B : HilbertOperator R),
        ⁅(B : HilbertOperator R), (A : HilbertOperator R)⁆⁆) +
      (s ^ 2 / 8) * opNorm (⁅(A : HilbertOperator R),
        ⁅(A : HilbertOperator R), (B : HilbertOperator R)⁆⁆) := by
  rw [strangDerivative, opNorm_smul, Complex.norm_I, one_mul]
  rw [opNorm_mul_unitaryGroup _ (timeEvolutionOp_mem_unitaryGroup A.2 (s / 2)),
    opNorm_mul_unitaryGroup _ (timeEvolutionOp_mem_unitaryGroup B.2 s), mul_assoc,
    opNorm_unitaryGroup_mul _ (timeEvolutionOp_mem_unitaryGroup (A.2.add B.2) (t - s)),
    opNorm_unitaryGroup_mul _ (timeEvolutionOp_mem_unitaryGroup A.2 (s / 2))]
  exact strangDefect_bound A B s hs

/-- The two-term bound is obtained by integrating the quadratic defect after
its linear terms cancel [CST+21, prefactor.tex:52-81]. -/
private lemma strang_twoTerm_bound {R : Register} (A B : Hamiltonian R)
    (t : ℝ) (ht : 0 ≤ t) :
    opNorm ((timeEvolution A (t / 2) * timeEvolution B t * timeEvolution A (t / 2) :
        HilbertOperator R) - (timeEvolution (A + B) t : HilbertOperator R)) ≤
      (t ^ 3 / 12) * opNorm (⁅(B : HilbertOperator R),
        ⁅(B : HilbertOperator R), (A : HilbertOperator R)⁆⁆) +
      (t ^ 3 / 24) * opNorm (⁅(A : HilbertOperator R),
        ⁅(A : HilbertOperator R), (B : HilbertOperator R)⁆⁆) := by
  let C := opNorm (⁅(B : HilbertOperator R),
    ⁅(B : HilbertOperator R), (A : HilbertOperator R)⁆⁆)
  let D := opNorm (⁅(A : HilbertOperator R),
    ⁅(A : HilbertOperator R), (B : HilbertOperator R)⁆⁆)
  have h := endpoint_bound (strangInterpolation (A : HilbertOperator R) B t)
    (strangDerivative (A : HilbertOperator R) B t)
    (fun s : ℝ => s ^ 2 * (C / 4 + D / 8)) t ht
    (hasDerivAt_strangInterpolation (A : HilbertOperator R) B t)
    (continuous_strangDerivative (A : HilbertOperator R) B t)
    ((continuous_id.pow 2).mul continuous_const) (by
      intro s hs
      have hb := strangDerivative_bound A B t s hs.1
      dsimp [C, D]
      convert hb using 1
      ring)
  have hi : (∫ s in (0 : ℝ)..t, s ^ 2 * (C / 4 + D / 8)) =
      t ^ 3 / 12 * C + t ^ 3 / 24 * D := by
    rw [intervalIntegral.integral_mul_const, integral_pow]
    norm_num
    ring
  rw [hi] at h
  simpa [strangInterpolation, C, D] using h

private lemma secondOrder_sum_succ {R : Register} {L : ℕ}
    (H : HamiltonianFamily R (L + 1)) :
    Hamiltonian.sum H = H 0 + Hamiltonian.sum (fun j : Fin L => H j.succ) := by
  apply Subtype.ext
  simp [Hamiltonian.coe_sum, Fin.sum_univ_succ]

/-- Compact second-order estimate with the weighted nested-commutator sum. -/
lemma secondOrder_error_bound_compact {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) (ht : 0 ≤ t) :
    opNorm ((secondOrderStep H t : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 3 / 12) * secondOrderCommutatorSum H := by
  induction L with
  | zero =>
    have hsum : Hamiltonian.sum H = 0 := by
      apply Subtype.ext
      simp
    simp [hsum, timeEvolutionOp]
  | succ L ih =>
    let T : HamiltonianFamily R L := fun j => H j.succ
    let S := Hamiltonian.sum T
    let P : HilbertOperator R := secondOrderStep T t
    let V : HilbertOperator R := timeEvolution S t
    let U : HilbertOperator R := timeEvolution (H 0) (t / 2)
    have hsum : Hamiltonian.sum H = H 0 + S := secondOrder_sum_succ H
    have htail : opNorm (P - V) ≤ (t ^ 3 / 12) * secondOrderCommutatorSum T := ih T
    have hpair := strang_twoTerm_bound (H 0) S t ht
    have hunit : U ∈ Matrix.unitaryGroup R.Index ℂ :=
      (timeEvolution (H 0) (t / 2)).property
    have hcancel : opNorm (U * P * U - U * V * U) = opNorm (P - V) := by
      rw [← sub_mul, ← mul_sub, opNorm_mul_unitaryGroup _ hunit,
        opNorm_unitaryGroup_mul _ hunit]
    rw [secondOrderStep_succ, hsum]
    change opNorm (U * P * U - (timeEvolution (H 0 + S) t : HilbertOperator R)) ≤ _
    calc
      _ ≤ opNorm (U * P * U - U * V * U) +
          opNorm (U * V * U - (timeEvolution (H 0 + S) t : HilbertOperator R)) :=
        opNorm_sub_le_add _ (U * V * U) _
      _ ≤ (t ^ 3 / 12) * secondOrderCommutatorSum T +
          ((t ^ 3 / 12) * opNorm (⁅(S : HilbertOperator R),
            ⁅(S : HilbertOperator R), (H 0 : HilbertOperator R)⁆⁆) +
          (t ^ 3 / 24) * opNorm (⁅(H 0 : HilbertOperator R),
            ⁅(H 0 : HilbertOperator R), (S : HilbertOperator R)⁆⁆)) := by
        rw [hcancel]
        exact add_le_add htail hpair
      _ = _ := by
        rw [secondOrderCommutatorSum_succ]
        dsimp [S, T]
        ring

/-- The finite-family second-order estimate with the exact coefficients
`1/12` and `1/24` [CST+21, prefactor.tex:105-114]. -/
public theorem secondOrder_error_bound {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) (ht : 0 ≤ t) :
    opNorm ((secondOrderStep H t : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 3 / 12) * (∑ j : Fin L, opNorm (⁅(∑ k : Fin L, if j < k then
        (H k : HilbertOperator R) else 0), ⁅(∑ k : Fin L, if j < k then
        (H k : HilbertOperator R) else 0), (H j : HilbertOperator R)⁆⁆)) +
      (t ^ 3 / 24) * ∑ j : Fin L, opNorm (⁅(H j : HilbertOperator R),
        ⁅(H j : HilbertOperator R), (∑ k : Fin L, if j < k then
          (H k : HilbertOperator R) else 0)⁆⁆) := by
  convert secondOrder_error_bound_compact H t ht using 1
  unfold secondOrderCommutatorSum
  ring

/-- Unitary telescoping gives the second-order `1/r²` repeated-step estimate,
with the nested-commutator normalization of [CST+21, prefactor.tex:105-114]. -/
lemma secondOrder_repeated_error_bound {R : Register} {L : ℕ}
    (H : HamiltonianFamily R L) (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    opNorm (((secondOrderStep H (t / (r : ℝ))) ^ r : HilbertOperator R) -
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R)) ≤
      (t ^ 3 / (12 * (r : ℝ) ^ 2)) * secondOrderCommutatorSum H := by
  let P := secondOrderStep H (t / (r : ℝ))
  let U := timeEvolution (Hamiltonian.sum H) (t / (r : ℝ))
  have htel := opNorm_pow_sub_pow_le P.property U.property r
  have hpow : (U : HilbertOperator R) ^ r =
      (timeEvolution (Hamiltonian.sum H) t : HilbertOperator R) :=
    timeEvolutionOp_pow_div _ (Nat.ne_zero_of_lt hr) t
  have hstep := secondOrder_error_bound_compact H (t / (r : ℝ))
    (div_nonneg ht (Nat.cast_nonneg _))
  have hscalar : (r : ℝ) * (((t / (r : ℝ)) ^ 3 / 12) * secondOrderCommutatorSum H) =
      (t ^ 3 / (12 * (r : ℝ) ^ 2)) * secondOrderCommutatorSum H := by
    field_simp [show (r : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hr)]
  calc
    _ = opNorm ((P : HilbertOperator R) ^ r - (U : HilbertOperator R) ^ r) := by
      rw [hpow]
    _ ≤ (r : ℝ) * opNorm ((P : HilbertOperator R) - (U : HilbertOperator R)) := htel
    _ ≤ (r : ℝ) * (((t / (r : ℝ)) ^ 3 / 12) * secondOrderCommutatorSum H) :=
      mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
    _ = _ := hscalar

end Trotter

end

end QuantumAlg
