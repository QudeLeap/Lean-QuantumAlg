/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base
public import QuantumAlg.Util.Polynomial.Laurent
import all QuantumAlg.Primitives.QSP.MultiQubit.QPP.Signal
import all QuantumAlg.Primitives.QSP.SingleQubit.Fourier

/-!
# QPP Laurent blocks

Ancilla-block algebra, Laurent operator semantics, and source complement certificates for QPP.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open NormalizedVector Module.End

noncomputable section

variable {n : ℕ}
variable {U : UnitaryOperator (Qubits n)}

/-! ### Ancilla block algebra for the source QPP word -/

/-- Ancilla-indexed block of a gate acting on one control qubit plus an
`n`-qubit system.  This is the block-matrix view used to prove that the same
QPP circuit supplies both the projected-block correctness statement and the
resource counters [WZYW23, arxiv_v3.tex:2446-2465]. -/
noncomputable def QPP.ancillaBlock (a b : Fin (2 ^ 1))
    (V : HilbertOperator (Qubits (1 + n))) : HilbertOperator (Qubits n) :=
  fun i j => V (prodEquiv (a, i)) (prodEquiv (b, j))

/-- For one ancilla qubit, the block-encoding `projectedBlock` is the
`|0⟩,|0⟩` ancilla block. -/
theorem QPP.projectedBlock_one_eq_ancillaBlock
    (V : HilbertOperator (Qubits (1 + n))) :
    projectedBlock 1 n V =
      QPP.ancillaBlock (n := n) 0 0 V := rfl

/-- Applying the one-ancilla projected block is the same as applying the full
gate to `|0> ⊗ ψ` and reading the `|0>` ancilla slice. -/
theorem QPP.projectedBlock_one_applyVec
    (V : HilbertOperator (Qubits (1 + n))) (ψ : HilbertVector (Qubits n)) :
    HilbertOperator.applyVec
        (projectedBlock 1 n V) ψ =
      fun i => (V.applyVec
        (HilbertVector.tensor (ket0 : HilbertVector (Qubits 1)) ψ))
          (prodEquiv ((0 : Fin (2 ^ 1)), i)) := by
  ext i
  rw [HilbertOperator.applyVec_apply, HilbertOperator.applyVec_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := 1) (n := n))]
  simp only [projectedBlock, ket0, NormalizedVector.ket, Nat.reducePow, Fin.isValue,
    HilbertVector.tensor_apply, Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  simp

/-- Ancilla blocks multiply as ordinary `2 × 2` block matrices. -/
theorem QPP.ancillaBlock_mul (a c : Fin (2 ^ 1))
    (V W : HilbertOperator (Qubits (1 + n))) :
    QPP.ancillaBlock a c (V * W) =
      ∑ b : Fin (2 ^ 1),
        QPP.ancillaBlock a b V * QPP.ancillaBlock b c W := by
  ext i j
  change
    (∑ z : Fin (2 ^ (1 + n)),
      V (prodEquiv (a, i)) z * W z (prodEquiv (c, j))) =
    (∑ b : Fin (2 ^ 1), ∑ x : Fin (2 ^ n),
      V (prodEquiv (a, i)) (prodEquiv (b, x)) *
        W (prodEquiv (b, x)) (prodEquiv (c, j)))
  rw [← Equiv.sum_comp (prodEquiv (m := 1) (n := n))]
  simp [Fintype.sum_prod_type]

/-- Ancilla block of a one-qubit operator tensored with the system identity. -/
theorem QPP.ancillaBlock_tensor_left (A : HilbertOperator (Qubits 1))
    (a b : Fin (2 ^ 1)) :
    QPP.ancillaBlock (n := n) a b
        (HilbertOperator.tensor A
          (1 : HilbertOperator (Qubits n))) =
      A a b • (1 : HilbertOperator (Qubits n)) := by
  ext i j
  simp only [QPP.ancillaBlock, HilbertOperator.tensor_apply]
  have hai := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := n)) (a, i)
  have hbj := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := n)) (b, j)
  rw [hai, hbj]
  change A a b * (1 : HilbertOperator (Qubits n)) i j =
    (A a b • (1 : HilbertOperator (Qubits n))) i j
  by_cases hij : i = j <;>
    simp [Matrix.one_apply, Matrix.smul_apply, hij]

/-- Ancilla blocks of the controlled-`U` gate. -/
theorem QPP.ancillaBlock_controlled (U : UnitaryOperator (Qubits n))
    (a b : Fin (2 ^ 1)) :
    QPP.ancillaBlock a b
        (UnitaryOperator.controlledQubits U : HilbertOperator (Qubits (1 + n))) =
      if a = b then
        if a = 0 then (1 : HilbertOperator (Qubits n)) else (U : HilbertOperator (Qubits n))
      else 0 := by
  ext i j
  fin_cases a <;> fin_cases b <;>
    by_cases hij : i = j <;>
      simp [QPP.ancillaBlock, UnitaryOperator.coe_controlledQubits,
        HilbertOperator.tensor_apply, HilbertOperator.proj0, HilbertOperator.proj1,
        Matrix.add_apply,
        Matrix.one_apply, hij]

/-- Ancilla blocks of the zero-branch controlled-`U` gate. -/
theorem QPP.ancillaBlock_controlledOnZero (U : UnitaryOperator (Qubits n))
    (a b : Fin (2 ^ 1)) :
    QPP.ancillaBlock a b
        (UnitaryOperator.controlledQubitsOnZero U :
          HilbertOperator (Qubits (1 + n))) =
      if a = b then
        if a = 0 then (U : HilbertOperator (Qubits n)) else (1 : HilbertOperator (Qubits n))
      else 0 := by
  ext i j
  fin_cases a <;> fin_cases b <;>
    by_cases hij : i = j <;>
      simp [QPP.ancillaBlock, UnitaryOperator.coe_controlledQubitsOnZero,
        HilbertOperator.tensor_apply, HilbertOperator.proj0, HilbertOperator.proj1,
        Matrix.add_apply,
        Matrix.one_apply, hij]

/-- Ancilla blocks of the initial one-qubit processing gate in Wang's
alternating QPP word. -/
theorem QPP.ancillaBlock_qppAlternatingInitialGate
    (a b : Fin (2 ^ 1)) (φ θ₀ φ₀ : ℝ) :
    QPP.ancillaBlock (n := n) a b
        ((qppAlternatingInitialGate n φ θ₀ φ₀).matrix :
          HilbertOperator (Qubits (1 + n))) =
      ((qspYZZYZInitialCircuit φ θ₀ φ₀).matrix :
        HilbertOperator (Qubits 1)) a b •
        (1 : HilbertOperator (Qubits n)) := by
  simpa using
    (QPP.ancillaBlock_tensor_left (n := n)
      (A := (qspYZZYZInitialCircuit φ θ₀ φ₀).matrix) a b)

/-- Ancilla-block recurrence for one source-aligned alternating QPP step.  It
keeps the controlled branch and the one-qubit processing block visible, which
is the form needed for the operator-valued Laurent recurrence
[WZYW23, arxiv_v3.tex:601-609,2446-2465]. -/
theorem QPP.ancillaBlock_qppAlternatingStepGate
    (U : UnitaryOperator (Qubits n)) (j : ℕ) (p : ℝ × ℝ)
    (a b : Fin (2 ^ 1)) :
    QPP.ancillaBlock a b
        (qppAlternatingStepGate U j p :
          HilbertOperator (Qubits (1 + n))) =
      ∑ c : Fin (2 ^ 1),
        (if j % 2 = 0 then
            (if a = c then
              if a = 0 then (U.dagger : HilbertOperator (Qubits n)) else 1
            else 0)
          else
            (if a = c then
              if a = 0 then (1 : HilbertOperator (Qubits n)) else U
            else 0)) *
          ((qppProcessingPairGate p : HilbertOperator (Qubits 1)) c b •
            (1 : HilbertOperator (Qubits n))) := by
  rw [qppAlternatingStepGate_operator, QPP.ancillaBlock_mul]
  by_cases hj : j % 2 = 0
  · rw [qppAlternatingOracleGate_matrix_of_even U hj,
      qppLiftProcessingGate_matrix]
    simp [hj,
      QPP.ancillaBlock_controlledOnZero, QPP.ancillaBlock_tensor_left]
  · rw [qppAlternatingOracleGate_matrix_of_odd U hj,
      qppLiftProcessingGate_matrix]
    simp [hj, QPP.ancillaBlock_controlled,
      QPP.ancillaBlock_tensor_left]

/-- The Laurent polynomial operator `F(U) = sum_{\ell=-L}^{L} c_\ell U^\ell`.
The index `k : Fin (2 * L + 1)` represents exponent `k - L`; negative powers
are written using `U†`, since `U` is unitary. -/
public def unitaryLaurentPolynomial (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) : HilbertOperator (Qubits n) :=
  ∑ k, coeff k •
    if k.val ≤ L then
      (U.dagger : HilbertOperator (Qubits n)) ^ (L - k.val)
    else
      (U : HilbertOperator (Qubits n)) ^ (k.val - L)

/-- Evaluate the degree-`≤ 2L` polynomial part of an even-length Laurent
encoding at the unitary `U`: coefficient `k` contributes the integer power
`U^(k-L)`, with negative powers written using `U†`.  This is the operator-side
counterpart of `lEval (2*L) A x`; the public coefficient family is the special
case `A = laurentCoeffPolynomial L coeff`. -/
noncomputable def QPP.operatorLaurentPolynomial (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (A : Polynomial ℂ) : HilbertOperator (Qubits n) :=
  ∑ k : Fin (2 * L + 1), A.coeff k.val •
    if k.val ≤ L then
      (U.dagger : HilbertOperator (Qubits n)) ^ (L - k.val)
    else
      (U : HilbertOperator (Qubits n)) ^ (k.val - L)

@[simp] theorem QPP.operatorLaurentPolynomial_zero
    (U : UnitaryOperator (Qubits n)) (A : Polynomial ℂ) :
    QPP.operatorLaurentPolynomial 0 U A =
      A.coeff 0 • (1 : HilbertOperator (Qubits n)) := by
  classical
  ext i j
  simp [QPP.operatorLaurentPolynomial]

theorem QPP.operatorLaurentPolynomial_add
    (L : ℕ) (U : UnitaryOperator (Qubits n)) (A B : Polynomial ℂ) :
    QPP.operatorLaurentPolynomial L U (A + B) =
      QPP.operatorLaurentPolynomial L U A +
        QPP.operatorLaurentPolynomial L U B := by
  classical
  simp only [QPP.operatorLaurentPolynomial, Polynomial.coeff_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k.val ≤ L <;> simp [hk, add_smul]

theorem QPP.operatorLaurentPolynomial_C_mul
    (L : ℕ) (U : UnitaryOperator (Qubits n)) (c : ℂ) (A : Polynomial ℂ) :
    QPP.operatorLaurentPolynomial L U (Polynomial.C c * A) =
      c • QPP.operatorLaurentPolynomial L U A := by
  classical
  simp only [QPP.operatorLaurentPolynomial, Polynomial.coeff_C_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k.val ≤ L <;> simp [hk, smul_smul]

theorem QPP.operatorLaurentPolynomial_sub
    (L : ℕ) (U : UnitaryOperator (Qubits n)) (A B : Polynomial ℂ) :
    QPP.operatorLaurentPolynomial L U (A - B) =
      QPP.operatorLaurentPolynomial L U A -
        QPP.operatorLaurentPolynomial L U B := by
  classical
  simp only [QPP.operatorLaurentPolynomial, Polynomial.coeff_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k.val ≤ L <;> simp [hk, sub_smul]

/-- Multiplying the Laurent coefficient polynomial by `X` shifts the center
from `L` to `L+1`.  The extra highest coefficient vanishes under the supplied
degree bound, so the represented operator is unchanged. -/
theorem QPP.operatorLaurentPolynomial_X_mul
    (L : ℕ) (U : UnitaryOperator (Qubits n)) (A : Polynomial ℂ)
    (hA : A.natDegree ≤ 2 * L) :
    QPP.operatorLaurentPolynomial (L + 1) U (Polynomial.X * A) =
      QPP.operatorLaurentPolynomial L U A := by
  classical
  simp only [QPP.operatorLaurentPolynomial, coeff_X_mul']
  rw [Fin.sum_univ_succ]
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, le_add_iff_nonneg_left,
    zero_le, tsub_zero, zero_smul, Fin.val_succ,
    Nat.add_eq_zero_iff, Fin.val_eq_zero_iff, one_ne_zero, and_false,
    add_tsub_cancel_right, add_le_add_iff_right, Nat.reduceSubDiff, smul_ite,
    zero_add]
  let term : ℕ → HilbertOperator (Qubits n) := fun k =>
    if k ≤ L then
      A.coeff k • (U.dagger : HilbertOperator (Qubits n)) ^ (L - k)
    else
      A.coeff k • (U : HilbertOperator (Qubits n)) ^ (k - L)
  change (∑ x : Fin (2 * (L + 1)), term x.val) =
    ∑ x : Fin (2 * L + 1), term x.val
  have hsize : 2 * (L + 1) = (2 * L + 1) + 1 := by omega
  calc
    (∑ x : Fin (2 * (L + 1)), term x.val)
        = ∑ x : Fin ((2 * L + 1) + 1), term x.val := by
            refine Fintype.sum_equiv (finCongr hsize) _ _ ?_
            intro x
            simp
    _ = (∑ x : Fin (2 * L + 1), term x.val) + term (2 * L + 1) := by
            simpa using
              (Fin.sum_univ_castSucc
                (fun x : Fin ((2 * L + 1) + 1) => term x.val))
    _ = ∑ x : Fin (2 * L + 1), term x.val := by
            have htop : A.coeff (2 * L + 1) = 0 := by
              exact Polynomial.coeff_eq_zero_of_natDegree_lt
                (lt_of_le_of_lt hA (by omega))
            have htail : term (2 * L + 1) = 0 := by
              simp [term, htop]
            simp [htail]

/-- Polynomial encoding of a Laurent coefficient family:
`lEval (2L) (laurentCoeffPolynomial L coeff)` is
`∑_{\ell=-L}^{L} c_\ell e^{i\ell x}` with index `k` representing
`ℓ = k - L`. -/
public noncomputable def QPP.laurentCoeffPolynomial (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) : Polynomial ℂ :=
  ∑ k : Fin (2 * L + 1), Polynomial.C (coeff k) *
    (Polynomial.X : Polynomial ℂ) ^ k.val

/-- The coefficient-family Laurent representative has degree at most its
budget `2L`. -/
theorem QPP.laurentCoeffPolynomial_natDegree_le (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) :
    (QPP.laurentCoeffPolynomial L coeff).natDegree ≤ 2 * L := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hne : ∀ k : Fin (2 * L + 1), m ≠ k.val := by
    intro k
    omega
  simp [QPP.laurentCoeffPolynomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, hne]

/-- Exponential shift for negative Laurent powers in the `lEval` encoding. -/
private theorem QPP.laurent_exp_shift_le (L k : ℕ) (θ : ℝ) (hk : k ≤ L) :
    Complex.exp (-(((L * θ : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((θ : ℂ) * Complex.I)) ^ (L - k) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  have hL : (L : ℂ) = (L - k : ℕ) + (k : ℂ) := by
    exact_mod_cast (Nat.sub_add_cancel hk).symm
  rw [hL]
  ring

/-- Exponential shift for positive Laurent powers in the `lEval` encoding. -/
private theorem QPP.laurent_exp_shift_gt (L k : ℕ) (θ : ℝ) (hk : ¬ k ≤ L) :
    Complex.exp (-(((L * θ : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((k * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) ^ (k - L) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  have hle : L ≤ k := le_of_lt (Nat.lt_of_not_ge hk)
  have hk' : (k : ℂ) = (k - L : ℕ) + (L : ℂ) := by
    exact_mod_cast (Nat.sub_add_cancel hle).symm
  rw [hk']
  ring

/-- Coefficient expansion of the Laurent polynomial value used by QPP. -/
theorem QPP.lEval_laurentCoeffPolynomial
    (L : ℕ) (coeff : Fin (2 * L + 1) → ℂ) (θ : ℝ) :
    lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) θ =
      ∑ k : Fin (2 * L + 1), coeff k *
        if k.val ≤ L then
          Complex.exp (-((θ : ℂ) * Complex.I)) ^ (L - k.val)
        else
          Complex.exp ((θ : ℂ) * Complex.I) ^ (k.val - L) := by
  classical
  simp only [lEval, QPP.laurentCoeffPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hbudget :
      Complex.exp (-(((↑(2 * L) * θ / 2 : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-(((L * θ : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    push_cast
    ring
  rw [hbudget]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k.val ≤ L
  · rw [if_pos hk]
    have hpow :
        Complex.exp ((θ : ℂ) * Complex.I) ^ k.val =
          Complex.exp (((k.val * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hpow]
    rw [← QPP.laurent_exp_shift_le L k.val θ hk]
    ring
  · rw [if_neg hk]
    have hpow :
        Complex.exp ((θ : ℂ) * Complex.I) ^ k.val =
          Complex.exp (((k.val * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hpow]
    rw [← QPP.laurent_exp_shift_gt L k.val θ hk]
    ring

/-- On the source eigenbasis of `U`, the Laurent operator evaluates to the
scalar Laurent value at the corresponding eigenphase. -/
theorem QPP.unitaryLaurentPolynomial_apply_phaseBasis
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (decomp : QPP.PhaseDecomposition U) (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec (unitaryLaurentPolynomial L U coeff) (decomp.basis j) =
      lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) (decomp.phase j) •
        decomp.basis j := by
  classical
  rw [QPP.lEval_laurentCoeffPolynomial]
  simp only [unitaryLaurentPolynomial]
  rw [HilbertOperator.sum_applyVec]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : k.val ≤ L
  · rw [if_pos hk]
    rw [HilbertOperator.smul_applyVec]
    have hpow := QPP.gate_applyVec_pow_eigenstate
      (U := U.dagger) (u := decomp.pure j)
      (lam := Complex.exp (-((decomp.phase j : ℂ) * Complex.I)))
      (QPP.conjTranspose_apply_eigenstate_phaseVec U (decomp.pure j)
        (decomp.phase j) (decomp.eigen_pure j))
      (L - k.val)
    change coeff k • HilbertOperator.applyVec
        ((U.dagger : HilbertOperator (Qubits n)) ^ (L - k.val))
        (decomp.basis j) =
      (coeff k *
        if k.val ≤ L then
          Complex.exp (-((decomp.phase j : ℂ) * Complex.I)) ^ (L - k.val)
        else
          Complex.exp ((decomp.phase j : ℂ) * Complex.I) ^ (k.val - L)) •
        decomp.basis j
    rw [← QPP.PhaseDecomposition.pure_coe decomp j]
    rw [hpow]
    simp [hk, smul_smul]
  · rw [if_neg hk]
    rw [HilbertOperator.smul_applyVec]
    have hpow := QPP.gate_applyVec_pow_eigenstate
      (U := U) (u := decomp.pure j)
      (lam := Complex.exp ((decomp.phase j : ℂ) * Complex.I))
      (decomp.eigen_pure j) (k.val - L)
    change coeff k • HilbertOperator.applyVec
        ((U : HilbertOperator (Qubits n)) ^ (k.val - L))
        (decomp.basis j) =
      (coeff k *
        if k.val ≤ L then
          Complex.exp (-((decomp.phase j : ℂ) * Complex.I)) ^ (L - k.val)
        else
          Complex.exp ((decomp.phase j : ℂ) * Complex.I) ^ (k.val - L)) •
        decomp.basis j
    rw [← QPP.PhaseDecomposition.pure_coe decomp j]
    rw [hpow]
    simp [hk, smul_smul]

/-- The public coefficient-family Laurent operator is the polynomial-operator
evaluation of `laurentCoeffPolynomial`. -/
theorem QPP.operatorLaurentPolynomial_laurentCoeffPolynomial
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) :
    QPP.operatorLaurentPolynomial L U
        (QPP.laurentCoeffPolynomial L coeff) =
      unitaryLaurentPolynomial L U coeff := by
  classical
  simp only [QPP.operatorLaurentPolynomial, unitaryLaurentPolynomial,
    QPP.laurentCoeffPolynomial]
  refine Finset.sum_congr rfl ?_
  intro k _
  have hcoeff :
      (∑ k' : Fin (2 * L + 1), if k.val = k'.val then coeff k' else (0 : ℂ)) =
        coeff k := by
    simpa [Fin.ext_iff] using
      (Finset.sum_ite_eq (s := (Finset.univ : Finset (Fin (2 * L + 1))))
        (a := k) (b := coeff))
  by_cases hk : k.val ≤ L <;> simp [hk, hcoeff]

/-- Base case of the QPP projected-block recurrence: before any alternating
controlled-`U`/`U†` query, the top-left ancilla block is exactly the initial
constant Laurent polynomial evaluated at `U`. -/
theorem QPP.projectedBlock_qppAlternatingControlledCircuit_nil
    (U : UnitaryOperator (Qubits n)) (φ θ₀ φ₀ : ℝ) :
    projectedBlock 1 n
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ []).matrix :
          HilbertOperator (Qubits (1 + n))) =
      QPP.operatorLaurentPolynomial 0 U
        (qspYZZYZGeneratedPair φ θ₀ φ₀ []).1 := by
  rw [QPP.projectedBlock_one_eq_ancillaBlock,
    qppAlternatingControlledCircuit_nil_matrix,
    QPP.ancillaBlock_qppAlternatingInitialGate,
    QPP.operatorLaurentPolynomial_zero]
  have hinitial :
      ((qspYZZYZInitialCircuit φ θ₀ φ₀).matrix :
        HilbertOperator (Qubits 1)) =
        (rotZStdOp φ : HilbertOperator (Qubits 1)) *
          ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
            (rotZStdOp φ₀ : HilbertOperator (Qubits 1))) :=
    qspYZZYZInitialCircuit_matrix φ θ₀ φ₀
  have hentry :
      ((
        (rotZStdOp φ : HilbertOperator (Qubits 1)) *
          ((rotYOp θ₀ : HilbertOperator (Qubits 1)) *
            (rotZStdOp φ₀ : HilbertOperator (Qubits 1)))) 0 0) =
        Complex.exp (-(↑φ / 2 * Complex.I)) *
          (Complex.cos (↑θ₀ / 2) *
            Complex.exp (-(↑φ₀ / 2 * Complex.I))) := by
    simp [rotZStdOp, rotZOp, rotYOp, Matrix.mul_apply, Fin.sum_univ_two]
  have hscalar :
      Complex.exp (-(↑φ / 2 * Complex.I)) *
        (Complex.cos (↑θ₀ / 2) *
          Complex.exp (-(↑φ₀ / 2 * Complex.I))) =
        (qspYZZYZGeneratedPair φ θ₀ φ₀ []).1.coeff 0 := by
    simp only [qspYZZYZGeneratedPair, List.foldl_nil,
      qspYZZYZInitialPair, Polynomial.coeff_C_zero, Complex.ofReal_cos,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_add]
    calc
      Complex.exp (-(↑φ / 2 * Complex.I)) *
          (Complex.cos (↑θ₀ / 2) * Complex.exp (-(↑φ₀ / 2 * Complex.I))) =
        Complex.cos (↑θ₀ / 2) *
          (Complex.exp (-(↑φ / 2 * Complex.I)) *
            Complex.exp (-(↑φ₀ / 2 * Complex.I))) := by
          ring
      _ = Complex.cos (↑θ₀ / 2) *
          Complex.exp (-(↑φ / 2 * Complex.I) + -(↑φ₀ / 2 * Complex.I)) := by
          rw [Complex.exp_add]
      _ = Complex.cos (↑θ₀ / 2) *
          Complex.exp (-((↑φ + ↑φ₀) / 2 * Complex.I)) := by
          congr 1
          ring_nf
  rw [hinitial, hentry, hscalar]

/-- Laurent-complement certificate in Wang's appendix form:
`|F(x)|² + |G(x)|² = 1` is represented by the `IsYZPair (2L)` normalization
used by trigonometric QSP [WZYW23, arxiv_v3.tex:2262-2274,2333-2340]. -/
structure QPP.LaurentComplementCertificate (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) where
  /-- Complement polynomial paired with the target Laurent representative. -/
  complement : Polynomial ℂ
  qsp_pair : IsYZPair (2 * L) (QPP.laurentCoeffPolynomial L coeff) complement

/-- Promote the quantum-free Laurent complement interface to the QSP pair
certificate needed by QPP. -/
def QPP.LaurentComplementCertificate.ofTrigonometricComplement
    (L : ℕ) (coeff : Fin (2 * L + 1) → ℂ)
    (cert :
      Complement.Laurent.ComplementCertificate (2 * L)
        (QPP.laurentCoeffPolynomial L coeff)) :
    QPP.LaurentComplementCertificate L coeff where
  complement := cert.complement
  qsp_pair :=
    { degA := Polynomial.natDegree_le_iff_degree_le.mp
        (QPP.laurentCoeffPolynomial_natDegree_le L coeff)
      degB := cert.degree_complement
      norm := cert.polynomial_normalization }

/-- Source QPP-evolution certificate for a concrete unitary `U`.  It records
the phases used by the Wang QPP circuit and the projected-block equality they
induce [WZYW23, arxiv_v3.tex:2446-2465]. -/
structure QPP.QppEvolutionCertificate (L : ℕ)
    (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) where
  /-- Initial source `Z` phase for the alternating QPP word. -/
  φ : ℝ
  /-- Initial source `Y` phase for the alternating QPP word. -/
  θ₀ : ℝ
  /-- Final initial-block source `Z` phase for the alternating QPP word. -/
  φ₀ : ℝ
  /-- Pairwise source phases used by the alternating controlled-query steps. -/
  ps : List (ℝ × ℝ)
  length_eq : ps.length = 2 * L
  block_eq :
    projectedBlock 1 n
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n))) =
      unitaryLaurentPolynomial L U coeff

/-- Build the QPP evolution certificate once the controlled-word block has
been proved to evaluate the polynomial pair generated by the same phase
schedule.  This isolates the remaining source theorem to the operator-valued
Laurent block recurrence. -/
noncomputable def QPP.qppEvolutionCertificateOfOperatorLaurent
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (hlen : ps.length = 2 * L)
    (hfirst :
      (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).1 =
        QPP.laurentCoeffPolynomial L coeff)
    (hblock :
      projectedBlock 1 n
          ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
            HilbertOperator (Qubits (1 + n))) =
        QPP.operatorLaurentPolynomial L U
          (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).1) :
    QPP.QppEvolutionCertificate L U coeff where
  φ := φ
  θ₀ := θ₀
  φ₀ := φ₀
  ps := ps
  length_eq := hlen
  block_eq := by
    rw [hblock, hfirst]
    exact QPP.operatorLaurentPolynomial_laurentCoeffPolynomial L U coeff

/-- Source-level bounded Laurent polynomial data for QPP.  The first field is
the public boundedness hypothesis; the second is the Laurent-complement
handoff from Wang's appendix [WZYW23, arxiv_v3.tex:2233-2274,2333-2340].

The multi-qubit QPP evolution block equality is derived later from this
complement plus a source spectral decomposition, so public endpoints can bind
the projected-block equality and the resource counts to the same counted
circuit. -/
structure QPP.BoundedLaurentPolynomial (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) where
  bounded :
    ∀ x : ℝ, ‖lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) x‖ ≤ 1
  /-- Laurent complement certificate derived from Wang's bounded source package. -/
  complement : QPP.LaurentComplementCertificate L coeff

/-- Public bounded trigonometric-polynomial hypothesis before the QSP
phase-synthesis step.  This is the Lean form of the source assumption
`|F(x)| ≤ 1`; the reciprocal-conjugate root algebra derives the Laurent
complement internally [WZYW23, arxiv_v3.tex:2237-2274]. -/
public structure QPP.TrigonometricPolynomialBound (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) where
  bounded :
    ∀ x : ℝ, ‖lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) x‖ ≤ 1

/-- Convert Wang's source root-class facts into the existing Laurent complement
package consumed by the QSP/QPP circuit construction. -/
noncomputable def QPP.TrigonometricPolynomialBound.toBoundedLaurentPolynomial
    {L : ℕ} {coeff : Fin (2 * L + 1) → ℂ}
    (h : QPP.TrigonometricPolynomialBound L coeff) :
    QPP.BoundedLaurentPolynomial L coeff where
  bounded := h.bounded
  complement := by
    have hproblem :
        Complement.Laurent.BoundedComplementProblem (2 * L)
          (QPP.laurentCoeffPolynomial L coeff) :=
      { degree_A := by
          exact Polynomial.natDegree_le_iff_degree_le.mp
            (QPP.laurentCoeffPolynomial_natDegree_le L coeff)
        bounded := h.bounded }
    have hhas :
        Complement.Laurent.Witness.HasComplement (2 * L)
          (QPP.laurentCoeffPolynomial L coeff) :=
      by
        by_cases hres0 :
            Complement.Laurent.residualPolynomial (2 * L)
              (QPP.laurentCoeffPolynomial L coeff) = 0
        · exact Complement.Laurent.Witness.hasComplement_of_residual_eq_zero hres0
        · exact
            hproblem.hasComplement_of_unitCircleEven_and_scalarQuotient hres0
              (fun z hz0 hunit =>
                Complement.Laurent.BoundedComplementProblem.residual_unitCircle_roots_even
                  hproblem hres0 hz0 hunit)
              (Complement.Laurent.BoundedComplementProblem.sourceScalarQuotient_real_nonnegative
                hproblem hres0).1
              (Complement.Laurent.BoundedComplementProblem.sourceScalarQuotient_real_nonnegative
                hproblem hres0).2
    exact
      QPP.LaurentComplementCertificate.ofTrigonometricComplement L coeff
        (Classical.choice hhas)

/-- Laurent-complement existence extracted from the bounded Laurent polynomial
source package [WZYW23, arxiv_v3.tex:2262-2274]. -/
theorem QPP.laurentComplement_exists (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    Nonempty (QPP.LaurentComplementCertificate L coeff) :=
  ⟨h.complement⟩

/-- Trigonometric-QSP projection phases obtained from the Laurent complement
[WZYW23, arxiv_v3.tex:2333-2340]. -/
theorem QPP.trigonometricQSPProjection_exists (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ),
      ps.length = 2 * L ∧
        ∀ x : ℝ,
          qspYZZYZ φ θ₀ φ₀ ps x =
            qspMatYZ (2 * L) (QPP.laurentCoeffPolynomial L coeff)
              h.complement.complement x := by
  exact (TrigonometricQuantumSignalProcessing.main
    (2 * L) (QPP.laurentCoeffPolynomial L coeff)
      h.complement.complement).mp h.complement.qsp_pair

/-- The bounded Laurent source package supplies a concrete phase schedule whose
recurrence-generated YZZYZ pair has the target Laurent polynomial as its first
component.  The second component is the complement from Wang's appendix. -/
theorem QPP.generatedPair_from_boundedLaurent
    (L : ℕ) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    ∃ φ θ₀ φ₀ : ℝ, ∃ ps : List (ℝ × ℝ),
      ps.length = 2 * L ∧
        (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).1 =
          QPP.laurentCoeffPolynomial L coeff ∧
        (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).2 =
          h.complement.complement := by
  rcases QPP.trigonometricQSPProjection_exists L coeff h with
    ⟨φ, θ₀, φ₀, ps, hlen, hmat⟩
  rcases qspYZZYZGeneratedPair_eq_of_matrix φ θ₀ φ₀ ps
      (QPP.laurentCoeffPolynomial L coeff) h.complement.complement
      (by simpa [hlen] using hmat) with ⟨hfirst, hsecond⟩
  exact ⟨φ, θ₀, φ₀, ps, hlen, hfirst, hsecond⟩

/-- On every eigenbasis vector, the projected block of the alternating QPP word
with a phase schedule realizing the target Laurent pair acts by the target
Laurent value. -/
theorem QPP.projectedBlock_qppAlternatingControlledCircuit_apply_phaseBasis
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (decomp : QPP.PhaseDecomposition U)
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (hlen : ps.length = 2 * L)
    (B : Polynomial ℂ)
    (hmat : ∀ x : ℝ,
      qspYZZYZ φ θ₀ φ₀ ps x =
        qspMatYZ (2 * L) (QPP.laurentCoeffPolynomial L coeff) B x)
    (j : Fin (2 ^ n)) :
    HilbertOperator.applyVec
        (projectedBlock 1 n
          ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
            HilbertOperator (Qubits (1 + n))))
        (decomp.basis j) =
      lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) (decomp.phase j) •
        decomp.basis j := by
  have hdecomp :=
    QPP.qppAlternating_eigenstate_decomposition_evenVec U (decomp.pure j)
      (decomp.phase j) (decomp.eigen_pure j) φ θ₀ φ₀ ps hlen
      (ket0 : HilbertVector (Qubits 1))
  have htop :
      ((qspYZZYZ φ θ₀ φ₀ ps (decomp.phase j)).applyVec
          (ket0 : HilbertVector (Qubits 1))) 0 =
        lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff) (decomp.phase j) := by
    have hq := congrArg
      (fun M : HilbertOperator (Qubits 1) =>
        HilbertOperator.applyVec M (ket0 : HilbertVector (Qubits 1)))
      (hmat (decomp.phase j))
    have hq0 := congrArg (fun v : HilbertVector (Qubits 1) => v 0) hq
    calc
      ((qspYZZYZ φ θ₀ φ₀ ps (decomp.phase j)).applyVec
          (ket0 : HilbertVector (Qubits 1))) 0 =
        (HilbertOperator.applyVec
          (qspMatYZ (2 * L) (QPP.laurentCoeffPolynomial L coeff) B
            (decomp.phase j))
          (ket0 : HilbertVector (Qubits 1))) 0 := by
            simpa [UnitaryOperator.applyVec] using hq0
      _ = lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff)
          (decomp.phase j) := by
            exact qspMatYZ_applyVec_ket0_zero L
              (QPP.laurentCoeffPolynomial L coeff) B (decomp.phase j)
  ext i
  change ((projectedBlock 1 n
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n)))).applyVec
        (decomp.basis j)).ofLp i =
    (lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff)
      (decomp.phase j) • decomp.basis j).ofLp i
  have hproj :=
    QPP.projectedBlock_one_applyVec
      (n := n)
      (V := (qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix)
      (ψ := decomp.basis j)
  have hcoord := congrArg
    (fun v : HilbertVector (Qubits (1 + n)) => v (prodEquiv ((0 : Fin (2 ^ 1)), i)))
    hdecomp
  rw [hproj]
  calc
    (HilbertOperator.applyVec
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n)))
        (ket0.vec.tensor (decomp.basis j))).ofLp (prodEquiv (0, i)) =
      ((qspYZZYZ φ θ₀ φ₀ ps (decomp.phase j)).applyVec
          (ket0 : HilbertVector (Qubits 1))) 0 * (decomp.basis j) i := by
        simpa [HilbertVector.tensor_apply_prod,
          QPP.PhaseDecomposition.pure_coe] using hcoord
    _ = lEval (2 * L) (QPP.laurentCoeffPolynomial L coeff)
          (decomp.phase j) * (decomp.basis j) i := by
        exact congrArg (fun z : ℂ => z * (decomp.basis j) i) htop

/-- The projected block of the source QPP word is the target Laurent polynomial
operator whenever the same phase schedule realizes the target Laurent pair. -/
theorem QPP.projectedBlock_qppAlternatingControlledCircuit_eq_unitaryLaurentPolynomial
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (decomp : QPP.PhaseDecomposition U)
    (φ θ₀ φ₀ : ℝ) (ps : List (ℝ × ℝ))
    (hlen : ps.length = 2 * L)
    (B : Polynomial ℂ)
    (hmat : ∀ x : ℝ,
      qspYZZYZ φ θ₀ φ₀ ps x =
        qspMatYZ (2 * L) (QPP.laurentCoeffPolynomial L coeff) B x) :
    projectedBlock 1 n
        ((qppAlternatingControlledCircuit U φ θ₀ φ₀ ps).matrix :
          HilbertOperator (Qubits (1 + n))) =
      unitaryLaurentPolynomial L U coeff := by
  apply HilbertOperator.ext_of_applyVec_eq_on_orthonormalBasis decomp.basis
  intro j
  rw [QPP.projectedBlock_qppAlternatingControlledCircuit_apply_phaseBasis
    L U coeff decomp φ θ₀ φ₀ ps hlen B hmat j]
  rw [QPP.unitaryLaurentPolynomial_apply_phaseBasis]

/-- Type-level package for the phase schedule generated from bounded Laurent
data.  This lets noncomputable definitions choose the source phase schedule
without eliminating a proposition-valued existential into data. -/
structure QPP.GeneratedPairCertificate (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) (B : Polynomial ℂ) where
  /-- Initial source `Z` phase selected by the generated pair. -/
  φ : ℝ
  /-- Initial source `Y` phase selected by the generated pair. -/
  θ₀ : ℝ
  /-- Final initial-block source `Z` phase selected by the generated pair. -/
  φ₀ : ℝ
  /-- Alternating-step phase pairs selected by the generated pair. -/
  ps : List (ℝ × ℝ)
  length_eq : ps.length = 2 * L
  first_eq :
    (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).1 =
      QPP.laurentCoeffPolynomial L coeff
  second_eq :
    (qspYZZYZGeneratedPair φ θ₀ φ₀ ps).2 = B

/-- The bounded Laurent package noncomputably determines a type-level generated
phase schedule certificate. -/
theorem QPP.generatedPairCertificate_nonempty
    (L : ℕ) (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff) :
    Nonempty (QPP.GeneratedPairCertificate L coeff h.complement.complement) := by
  rcases QPP.generatedPair_from_boundedLaurent L coeff h with
    ⟨φ, θ₀, φ₀, ps, hlen, hfirst, hsecond⟩
  exact ⟨
    { φ := φ
      θ₀ := θ₀
      φ₀ := φ₀
      ps := ps
      length_eq := hlen
      first_eq := hfirst
      second_eq := hsecond }⟩

/-- The bounded Laurent source package plus a source spectral decomposition of
`U` generate the QPP evolution certificate internally.  The certificate is
therefore no longer a public hypothesis of `QPP.Witness.main`; it is derived
from the same phase schedule that supplies the counted QPP circuit. -/
noncomputable def QPP.qppEvolutionCertificateOfBoundedLaurent
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QPP.BoundedLaurentPolynomial L coeff)
    (decomp : QPP.PhaseDecomposition U) :
    QPP.QppEvolutionCertificate L U coeff := by
  classical
  let data :=
    Classical.choice (QPP.generatedPairCertificate_nonempty L coeff h)
  have hmat : ∀ x : ℝ,
      qspYZZYZ data.φ data.θ₀ data.φ₀ data.ps x =
        qspMatYZ (2 * L) (QPP.laurentCoeffPolynomial L coeff)
          h.complement.complement x := by
    intro x
    simpa [data.length_eq, data.first_eq, data.second_eq] using
      qspYZZYZ_eq_qspMatYZ_generatedPair data.φ data.θ₀ data.φ₀ data.ps x
  refine
    { φ := data.φ
      θ₀ := data.θ₀
      φ₀ := data.φ₀
      ps := data.ps
      length_eq := data.length_eq
      block_eq := ?_ }
  exact
    QPP.projectedBlock_qppAlternatingControlledCircuit_eq_unitaryLaurentPolynomial
      L U coeff decomp data.φ data.θ₀ data.φ₀ data.ps data.length_eq
      h.complement.complement hmat

namespace QPP.Complement

/-- Namespace-local spelling of the QPP Laurent polynomial operator. -/
abbrev unitaryLaurentPolynomial (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) : HilbertOperator (Qubits n) :=
  QuantumAlg.QSP.MultiQubit.unitaryLaurentPolynomial L U coeff

/-- Namespace-local spelling of the QPP Laurent complement certificate. -/
abbrev LaurentComplementCertificate (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.LaurentComplementCertificate L coeff

/-- Namespace-local spelling of the QPP evolution certificate. -/
abbrev QppEvolutionCertificate (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.QppEvolutionCertificate L U coeff

/-- Namespace-local spelling of bounded Laurent source data. -/
abbrev BoundedLaurentPolynomial (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.BoundedLaurentPolynomial L coeff

/-- Namespace-local spelling of the bounded trigonometric-polynomial public
hypothesis before complement extraction. -/
abbrev TrigonometricPolynomialBound (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.TrigonometricPolynomialBound L coeff

/-- Namespace-local spelling of generated phase-pair certificates. -/
abbrev GeneratedPairCertificate (L : ℕ)
    (coeff : Fin (2 * L + 1) → ℂ) (B : Polynomial ℂ) :=
  QuantumAlg.QSP.MultiQubit.QPP.GeneratedPairCertificate L coeff B

/-- Namespace-local constructor for QPP evolution from bounded Laurent data. -/
noncomputable abbrev qppEvolutionCertificateOfBoundedLaurent
    (L : ℕ) (U : UnitaryOperator (Qubits n))
    (coeff : Fin (2 * L + 1) → ℂ)
    (h : QuantumAlg.QSP.MultiQubit.QPP.BoundedLaurentPolynomial L coeff)
    (decomp : QuantumAlg.QSP.MultiQubit.QPP.PhaseDecomposition U) :
    QuantumAlg.QSP.MultiQubit.QPP.QppEvolutionCertificate L U coeff :=
  QuantumAlg.QSP.MultiQubit.QPP.qppEvolutionCertificateOfBoundedLaurent
    L U coeff h decomp

end QPP.Complement



end

end QSP.MultiQubit

end QuantumAlg

end
