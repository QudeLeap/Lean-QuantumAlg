/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Cost
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Core.Components.Control
public import QuantumAlg.Core.Components.Kets
public import QuantumAlg.Core.Components.Oracle.BlockEncoding
public import QuantumAlg.Core.Components.Oracle.Reflection
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
public import QuantumAlg.Util.Polynomial
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# QSVT spectral and projected-block support

Reusable polynomial, spectral, and projected-block support for projected QSVT.
-/

@[expose] public section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT


/-- Evaluate a complex polynomial on a finite-dimensional Hilbert operator via
Mathlib's algebraic polynomial evaluation. -/
noncomputable def polynomialOperator {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) : HilbertOperator (Qubits n) :=
  Polynomial.aeval A P

/-- Polynomial evaluation on a diagonal matrix is pointwise evaluation on the
diagonal entries.  This is the finite-dimensional algebraic core used to connect
the QSVT polynomial statement with Mathlib's Hermitian spectral theorem. -/
theorem diagonal_aeval_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Polynomial ℂ) (d : ι → ℂ) :
    Polynomial.aeval (Matrix.diagonal d) P =
      Matrix.diagonal (fun i => P.eval (d i)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases h : i = j <;>
        simp [h]
  | monomial k c =>
      ext i j
      by_cases h : i = j <;>
        simp [Matrix.algebraMap_matrix_apply, Matrix.diagonal_pow, h]

/-- Spectral form of polynomial evaluation on a Hermitian matrix: `P(A)` is
diagonalized by the same eigenbasis as `A`, with eigenvalues transformed by
`P`. -/
theorem polynomialOperator_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Polynomial ℂ) (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Polynomial.aeval A P =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => P.eval ((hA.eigenvalues i : ℝ) : ℂ))) := by
  calc
    Polynomial.aeval A P =
        Polynomial.aeval
          (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
            (Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)))) P := by
          exact congrArg (fun B => Polynomial.aeval B P) hA.spectral_theorem
    _ =
        Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Polynomial.aeval
            (Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ))) P) := by
          rw [Polynomial.aeval_algHom_apply]
    _ =
        Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (fun i => P.eval ((hA.eigenvalues i : ℝ) : ℂ))) := by
          rw [diagonal_aeval_polynomial]

/-! ### Scalar contraction dilation -/

/-- The standard one-qubit unitary dilation of a scalar contraction `p`.
The top-left entry is `p`; the remaining entries are chosen so the matrix is
unitary whenever `|p| <= 1`. -/
noncomputable def scalarDilationOp (p : ℂ) : HilbertOperator (Qubits 1) :=
  let r : ℂ := (Real.sqrt (1 - Complex.normSq p) : ℝ)
  !![p, r; -r, star p]

/-- The scalar dilation is unitary under the contraction side condition. -/
theorem scalarDilationOp_mem_unitaryGroup (p : ℂ) (hp : Complex.normSq p <= 1) :
    scalarDilationOp p ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hs : Real.sqrt (1 - Complex.normSq p) * Real.sqrt (1 - Complex.normSq p) =
      1 - Complex.normSq p := by
    rw [← sq, Real.sq_sqrt]
    linarith
  have hsC :
      ((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ) *
          ((Real.sqrt (1 - Complex.normSq p) : ℝ) : ℂ) =
        ((1 - Complex.normSq p : ℝ) : ℂ) := by
    exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply, hsC, Complex.mul_conj]
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply]
    ring
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply]
    ring
  · simp [scalarDilationOp, Matrix.mul_apply, Matrix.star_apply, hsC,
      Complex.normSq_eq_conj_mul_self]

@[simp]
theorem scalarDilationOp_block_entry (p : ℂ) : scalarDilationOp p 0 0 = p := by
  simp [scalarDilationOp]

/-- Bundled scalar dilation gate. -/
noncomputable def scalarDilation (p : ℂ) (hp : Complex.normSq p <= 1) : Gate (Qubits 1) :=
  Gate.ofUnitary (scalarDilationOp p) (scalarDilationOp_mem_unitaryGroup p hp)

@[simp]
theorem scalarDilation_block_entry (p : ℂ) (hp : Complex.normSq p <= 1) :
    (scalarDilation p hp : HilbertOperator (Qubits 1)) 0 0 = p := by
  simp [scalarDilation, scalarDilationOp]

/-- Block-diagonal direct sum of scalar dilations over a finite index set. -/
noncomputable def diagonalScalarDilationOp {ι : Type*} [DecidableEq ι]
    (p : ι → ℂ) : Matrix (Fin (2 ^ 1) × ι) (Fin (2 ^ 1) × ι) ℂ :=
  Matrix.of fun r s =>
    if r.2 = s.2 then scalarDilationOp (p r.2) r.1 s.1 else 0

/-- A direct sum of scalar contraction dilations is unitary. -/
theorem diagonalScalarDilationOp_mem_unitaryGroup {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ι → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    diagonalScalarDilationOp p ∈ Matrix.unitaryGroup (Fin (2 ^ 1) × ι) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext r s
  rw [Matrix.mul_apply]
  by_cases hrs : r.2 = s.2
  · have hsr : s.2 = r.2 := hrs.symm
    have hunit := scalarDilationOp_mem_unitaryGroup (p r.2) (hp r.2)
    rw [Matrix.mem_unitaryGroup_iff] at hunit
    have hentry := congrFun (congrFun hunit r.1) s.1
    rw [Matrix.mul_apply] at hentry
    rw [Fintype.sum_prod_type]
    have hcollapse :
        (∑ x : Fin (2 ^ 1), ∑ y : ι,
            diagonalScalarDilationOp p r (x, y) *
              star (diagonalScalarDilationOp p) (x, y) s) =
          ∑ x : Fin (2 ^ 1),
            scalarDilationOp (p r.2) r.1 x *
              star (scalarDilationOp (p r.2)) x s.1 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single r.2]
      · unfold diagonalScalarDilationOp
        rw [Matrix.star_apply]
        rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, if_pos hsr]
        rw [hsr]
        rw [Matrix.star_apply]
      · intro y _ hy
        have hyr : ¬r.2 = y := fun h => hy h.symm
        unfold diagonalScalarDilationOp
        rw [Matrix.of_apply, if_neg hyr, zero_mul]
      · intro hmissing
        exact False.elim (hmissing (Finset.mem_univ r.2))
    have hone :
        (1 : Matrix (Fin (2 ^ 1) × ι) (Fin (2 ^ 1) × ι) ℂ) r s =
          (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ) r.1 s.1 := by
      rw [Matrix.one_apply, Matrix.one_apply]
      by_cases h1 : r.1 = s.1
      · have hpairs : r = s := Prod.ext h1 hrs
        simp [hpairs]
      · have hpairs : r ≠ s := fun h => h1 (congrArg Prod.fst h)
        simp [hpairs, h1]
    rw [hcollapse, hone]
    exact hentry
  · rw [Fintype.sum_prod_type]
    have hsr : ¬s.2 = r.2 := fun h => hrs h.symm
    have hpair : r ≠ s := fun h => hrs (congrArg Prod.snd h)
    rw [Finset.sum_eq_zero]
    · rw [Matrix.one_apply]
      simp [hpair]
    · intro x _
      rw [Finset.sum_eq_zero]
      intro y _
      by_cases hyr : r.2 = y
      · have hsy : ¬s.2 = y := fun h => hrs (hyr.trans h.symm)
        unfold diagonalScalarDilationOp
        rw [Matrix.star_apply]
        rw [Matrix.of_apply, Matrix.of_apply, if_pos hyr, if_neg hsy, star_zero, mul_zero]
      · unfold diagonalScalarDilationOp
        rw [Matrix.of_apply, if_neg hyr, zero_mul]

/-- Reindexing rows and columns by the same equivalence preserves unitarity. -/
theorem reindex_mem_unitaryGroup {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) :
    Matrix.reindex e e M ∈ Matrix.unitaryGroup κ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hM ⊢
  rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    hM, Matrix.submatrix_one_equiv]

/-- The direct-sum scalar dilation reindexed to the `(1+n)`-qubit
ancilla-system basis. -/
noncomputable def diagonalScalarDilationQubitOp {n : Nat}
    (p : Fin (2 ^ n) → ℂ) : HilbertOperator (Qubits (1 + n)) :=
  Matrix.reindex (prodEquiv (m := 1) (n := n)) (prodEquiv (m := 1) (n := n))
    (diagonalScalarDilationOp p)

theorem diagonalScalarDilationQubitOp_mem_unitaryGroup {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    diagonalScalarDilationQubitOp p ∈ Matrix.unitaryGroup (Fin (2 ^ (1 + n))) ℂ :=
  reindex_mem_unitaryGroup (prodEquiv (m := 1) (n := n))
    (diagonalScalarDilationOp p) (diagonalScalarDilationOp_mem_unitaryGroup p hp)

/-- Gate (Qubits form) of the qubit-indexed direct-sum scalar dilation. -/
noncomputable def diagonalScalarDilationGate {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) : Gate (Qubits (1 + n)) :=
  Gate.ofUnitary (diagonalScalarDilationQubitOp p)
    (diagonalScalarDilationQubitOp_mem_unitaryGroup p hp)

/-- The top-left ancilla block of the qubit-indexed direct-sum scalar dilation
is the diagonal matrix of scalar entries. -/
theorem diagonalScalarDilationGate_projectedBlock {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    projectedBlock 1 n (diagonalScalarDilationGate p hp : HilbertOperator (Qubits (1 + n))) =
      Matrix.diagonal p := by
  ext i j
  unfold projectedBlock diagonalScalarDilationGate diagonalScalarDilationQubitOp
  simp [diagonalScalarDilationOp, Matrix.diagonal]

theorem diagonalScalarDilationGate_exactBlockEncoding {n : Nat}
    (p : Fin (2 ^ n) → ℂ) (hp : ∀ i, Complex.normSq (p i) <= 1) :
    ExactBlockEncoding 1 n (diagonalScalarDilationGate p hp) (Matrix.diagonal p) := by
  constructor
  intro i j
  rw [diagonalScalarDilationGate_projectedBlock]

theorem left_tensor_one_apply_zero {a n : Nat} (V : Gate (Qubits n))
    (i y : Fin (2 ^ n)) (x : Fin (2 ^ a)) :
    (Gate.tensor (1 : Gate (Qubits a)) V : Gate (Qubits (a + n)))
      (prodEquiv (0, i)) (prodEquiv (x, y)) =
      (if x = 0 then V i y else 0) := by
  by_cases hx : x = 0
  · subst x
    simp [Gate.tensor_apply]
  · have h0x : ¬(0 : Fin (2 ^ a)) = x := fun h => hx h.symm
    simp [Gate.tensor_apply, hx, h0x]

theorem right_tensor_one_apply_zero {a n : Nat} (V : Gate (Qubits n))
    (x : Fin (2 ^ a)) (y j : Fin (2 ^ n)) :
    (Gate.tensor (1 : Gate (Qubits a)) V.conjTranspose : Gate (Qubits (a + n)))
      (prodEquiv (x, y)) (prodEquiv (0, j)) =
      (if x = 0 then (V : HilbertOperator (Qubits n)).conjTranspose y j else 0) := by
  by_cases hx : x = 0 <;> simp [Gate.tensor_apply, hx]

theorem left_tensor_sum_collapse {a n : Nat} (V : Gate (Qubits n)) (D : Gate (Qubits (a + n)))
    (i y : Fin (2 ^ n)) :
    (∑ z : Fin (2 ^ (a + n)),
      if (0 : Fin (2 ^ a)) = (prodEquiv.symm z).1 then
        V i (prodEquiv.symm z).2 * D z (prodEquiv (0, y))
      else 0) =
      ∑ x : Fin (2 ^ n), V i x * D (prodEquiv (0, x)) (prodEquiv (0, y)) := by
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [Fintype.sum_prod_type]

theorem projectedBlock_system_conjugate
    {a n : Nat} (V : Gate (Qubits n)) (D : Gate (Qubits (a + n))) :
    projectedBlock a n
        ((Gate.tensor (1 : Gate (Qubits a)) V) * D *
            (Gate.tensor (1 : Gate (Qubits a)) V.conjTranspose) :
          HilbertOperator (Qubits (a + n))) =
      (V : HilbertOperator (Qubits n)) *
        projectedBlock a n (D : HilbertOperator (Qubits (a + n))) *
        (V : HilbertOperator (Qubits n)).conjTranspose := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply, Gate.coe_conjTranspose,
    Gate.tensor_apply, Gate.coe_one, Matrix.one_apply, Matrix.conjTranspose_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [Fintype.sum_prod_type, left_tensor_sum_collapse]

/-- The eigenbasis unitary of a Hermitian operator, bundled as a `Gate`. -/
noncomputable def eigenbasisGate {n : Nat} (A : HilbertOperator (Qubits n))
    (hA : A.IsHermitian) : Gate (Qubits n) :=
  Gate.ofUnitary (hA.eigenvectorUnitary : HilbertOperator (Qubits n))
    hA.eigenvectorUnitary.property

/-- The eigenvalue-level polynomial data used by the Hermitian spectral
construction. -/
noncomputable def hermitianPolynomialEigenvalues {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) : Fin (2 ^ n) → ℂ :=
  fun i => P.eval ((hA.eigenvalues i : ℝ) : ℂ)

/-- A constructive unitary dilation of `P(A)` obtained by diagonalizing the
Hermitian operator, dilating each transformed eigenvalue, and conjugating back
to the computational basis. -/
noncomputable def hermitianPolynomialDilationGate {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    Gate (Qubits (1 + n)) :=
  Gate.tensor (1 : Gate (Qubits 1)) (eigenbasisGate A hA)
    * diagonalScalarDilationGate (hermitianPolynomialEigenvalues P A hA) hcontract
    * (Gate.tensor (1 : Gate (Qubits 1)) (eigenbasisGate A hA).conjTranspose)

theorem hermitianPolynomialDilation_projectedBlock {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    projectedBlock 1 n
        (hermitianPolynomialDilationGate P A hA hcontract : HilbertOperator (Qubits (1 + n))) =
      polynomialOperator P A := by
  unfold hermitianPolynomialDilationGate
  change projectedBlock 1 n
      (((Gate.tensor (1 : Gate (Qubits 1)) (eigenbasisGate A hA))
          * diagonalScalarDilationGate (hermitianPolynomialEigenvalues P A hA) hcontract
          * (Gate.tensor (1 : Gate (Qubits 1)) (eigenbasisGate A hA).conjTranspose)) :
        HilbertOperator (Qubits (1 + n))) =
      polynomialOperator P A
  rw [projectedBlock_system_conjugate,
    diagonalScalarDilationGate_projectedBlock]
  rw [polynomialOperator, polynomialOperator_spectral P A hA]
  simp [eigenbasisGate, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  congr 2

theorem hermitianPolynomialDilation_exactBlockEncoding {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    ExactBlockEncoding 1 n (hermitianPolynomialDilationGate P A hA hcontract)
      (polynomialOperator P A) := by
  constructor
  intro i j
  rw [hermitianPolynomialDilation_projectedBlock]

theorem hermitian_eigenvalue_norm_le_of_operator_norm_le_one {n : Nat}
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) (hnorm : ‖A‖ ≤ 1)
    (i : Fin (2 ^ n)) :
    ‖(hA.eigenvalues i : ℝ)‖ ≤ 1 := by
  have hspec : hA.eigenvalues i ∈ spectrum ℝ A :=
    hA.eigenvalues_mem_spectrum_real i
  exact (spectrum.norm_le_norm_of_mem hspec).trans hnorm

theorem hermitian_eigenvalue_mem_Icc_of_operator_norm_le_one {n : Nat}
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) (hnorm : ‖A‖ ≤ 1)
    (i : Fin (2 ^ n)) :
    hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnorm_i := hermitian_eigenvalue_norm_le_of_operator_norm_le_one A hA hnorm i
  simpa [Real.norm_eq_abs] using (abs_le.mp hnorm_i)

theorem hermitianPolynomialEigenvalues_contract_of_bound {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hnorm : ‖A‖ ≤ 1)
    (hbound :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) ≤ 1 := by
  intro i
  exact hbound (hA.eigenvalues i)
    (hermitian_eigenvalue_mem_Icc_of_operator_norm_le_one A hA hnorm i)

@[simp]
theorem polynomialOperator_X {n : Nat} (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.X : Polynomial ℂ) A = A := by
  simp [polynomialOperator]

@[simp]
theorem polynomialOperator_C {n : Nat} (c : ℂ) (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.C c : Polynomial ℂ) A =
      c • (1 : HilbertOperator (Qubits n)) := by
  ext i j
  by_cases h : i = j <;>
    simp [polynomialOperator, Matrix.algebraMap_matrix_apply, Matrix.smul_apply, h]

@[simp]
theorem polynomialOperator_C_mul {n : Nat} (c : ℂ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.C c * P) A = c • polynomialOperator P A := by
  ext i j
  simp [polynomialOperator, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
    Matrix.smul_apply]

/-- A constant polynomial acts as its scalar multiple of the identity under
functional calculus. -/
theorem polynomialOperator_eq_scalar_one_of_natDegree_eq_zero {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (hdeg : P.natDegree = 0) :
    polynomialOperator P A = P.coeff 0 • (1 : HilbertOperator (Qubits n)) := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, polynomialOperator_C]
  simp

/-- Elementary eigenvector support lemma: powers of an operator preserve an
eigenvector with the corresponding powered eigenvalue. -/
theorem operatorPower_applyVec_of_eigenvector {N : Nat}
    (A : HilbertOperator (Qubits N)) (lambda : Complex)
    (v : StateVector (Qubits N))
    (hA : HilbertOperator.applyVec A v = lambda • v) (k : Nat) :
    HilbertOperator.applyVec (A ^ k) v = lambda ^ k • v := by
  induction k with
  | zero =>
      simp [HilbertOperator.one_applyVec]
  | succ k ih =>
      rw [pow_succ, HilbertOperator.mul_applyVec, hA,
        HilbertOperator.applyVec_smul, ih, smul_smul]
      ring_nf

/-- Elementary eigenvector support lemma for polynomial functional calculus:
if `v` is an eigenvector of `A` with eigenvalue `lambda`, then `P(A)` acts on
`v` by the scalar `P(lambda)`. -/
theorem polynomialOperator_applyVec_of_eigenvector {N : Nat}
    (P : Polynomial Complex) (A : HilbertOperator (Qubits N))
    (lambda : Complex) (v : StateVector (Qubits N))
    (hA : HilbertOperator.applyVec A v = lambda • v) :
    HilbertOperator.applyVec (polynomialOperator P A) v = P.eval lambda • v := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [polynomialOperator, map_add, HilbertOperator.add_applyVec, Polynomial.eval_add]
      rw [add_smul]
      rw [show ((Polynomial.aeval A) p).applyVec v = p.eval lambda • v by
        simpa [polynomialOperator] using hp]
      rw [show ((Polynomial.aeval A) q).applyVec v = q.eval lambda • v by
        simpa [polynomialOperator] using hq]
  | monomial k c =>
      have hscalar :
          ∀ w : StateVector (Qubits N),
            HilbertOperator.applyVec
              ((algebraMap Complex (HilbertOperator (Qubits N))) c) w =
                c • w := by
        intro w
        have hmat :
            ((algebraMap Complex (HilbertOperator (Qubits N))) c) =
              c • (1 : HilbertOperator (Qubits N)) := by
          ext i j
          by_cases h : i = j <;>
            simp [Matrix.algebraMap_matrix_apply, Matrix.smul_apply, h]
        rw [hmat, HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec]
      rw [polynomialOperator, Polynomial.aeval_monomial, Polynomial.eval_monomial]
      rw [HilbertOperator.mul_applyVec,
        operatorPower_applyVec_of_eigenvector A lambda v hA k,
        hscalar, smul_smul]

theorem polynomialOperator_add {n : Nat} (P Q : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (P + Q) A = polynomialOperator P A + polynomialOperator Q A := by
  simp [polynomialOperator]

theorem polynomialOperator_smul {n : Nat} (c : ℂ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (c • P) A = c • polynomialOperator P A := by
  rw [Polynomial.smul_eq_C_mul, polynomialOperator_C_mul]

/-- Polynomial functional calculus respects the real/imaginary and even/odd
coefficient split used in the arbitrary-parity QSVT reduction. This is an
elementary bookkeeping lemma supporting the four component construction in
[GSLW19, BlockHam.tex:1936-1952]. -/
theorem polynomialOperator_complex_fourPart_recompose {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
      polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A +
      (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
        Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A) =
      polynomialOperator P A := by
  let PReEven : Polynomial ℂ :=
    realPolynomialToComplex
      (realPolynomialEvenPart (complexPolynomialRealPart P))
  let PReOdd : Polynomial ℂ :=
    realPolynomialToComplex
      (realPolynomialOddPart (complexPolynomialRealPart P))
  let PImEven : Polynomial ℂ :=
    realPolynomialToComplex
      (realPolynomialEvenPart (complexPolynomialImagPart P))
  let PImOdd : Polynomial ℂ :=
    realPolynomialToComplex
      (realPolynomialOddPart (complexPolynomialImagPart P))
  let Psplit : Polynomial ℂ :=
    PReEven + PReOdd + (Polynomial.C Complex.I * PImEven +
      Polynomial.C Complex.I * PImOdd)
  have hsplit : Psplit = P := by
    simpa [Psplit, PReEven, PReOdd, PImEven, PImOdd] using
      complexPolynomial_fourPart_recompose P
  calc
    polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
      polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A +
      (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
        Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A)
        = polynomialOperator Psplit A := by
          simp [Psplit, PReEven, PReOdd, PImEven, PImOdd, polynomialOperator_add,
            polynomialOperator_C_mul]
    _ = polynomialOperator P A := by
          rw [hsplit]

/-- Averaging the four real/imaginary even/odd functional-calculus branches
gives the normalization-four target used by the complex Hermitian QSVT public
statement [GSLW19, BlockHam.tex:1936-1952]. -/
theorem polynomialOperator_complex_fourPart_average_recompose {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    (1 / 4 : ℂ) • polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
      (1 / 4 : ℂ) • polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A +
      ((1 / 4 : ℂ) • (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) +
        (1 / 4 : ℂ) • (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A)) =
      (1 / 4 : ℂ) • polynomialOperator P A := by
  calc
    (1 / 4 : ℂ) • polynomialOperator
        (realPolynomialToComplex
          (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
      (1 / 4 : ℂ) • polynomialOperator
        (realPolynomialToComplex
          (realPolynomialOddPart (complexPolynomialRealPart P))) A +
      ((1 / 4 : ℂ) • (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialEvenPart (complexPolynomialImagPart P))) A) +
        (1 / 4 : ℂ) • (Complex.I • polynomialOperator
          (realPolynomialToComplex
            (realPolynomialOddPart (complexPolynomialImagPart P))) A))
        = (1 / 4 : ℂ) •
            (polynomialOperator
                (realPolynomialToComplex
                  (realPolynomialEvenPart (complexPolynomialRealPart P))) A +
              polynomialOperator
                (realPolynomialToComplex
                  (realPolynomialOddPart (complexPolynomialRealPart P))) A +
              (Complex.I • polynomialOperator
                  (realPolynomialToComplex
                    (realPolynomialEvenPart (complexPolynomialImagPart P))) A +
                Complex.I • polynomialOperator
                  (realPolynomialToComplex
                    (realPolynomialOddPart (complexPolynomialImagPart P))) A)) := by
          ext i j
          simp [Matrix.add_apply, Matrix.smul_apply]
          ring
    _ = (1 / 4 : ℂ) • polynomialOperator P A := by
          rw [polynomialOperator_complex_fourPart_recompose P A]

/-- Averaging the doubled even and odd real parts reconstructs `P(A)`.
This is the polynomial-functional-calculus bookkeeping behind the real
arbitrary-parity reduction in `thm:arbParity`
[GSLW19, BlockHam.tex:1936-1951]. -/
theorem polynomialOperator_real_evenOdd_double_average_recompose {n : Nat}
    (PRe : Polynomial ℝ) (A : HilbertOperator (Qubits n)) :
    (1 / 2 : ℂ) • polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialEvenPart PRe)) A +
      (1 / 2 : ℂ) • polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialOddPart PRe)) A =
      polynomialOperator (realPolynomialToComplex PRe) A := by
  have hpoly :
      (1 / 2 : ℂ) • realPolynomialToComplex ((2 : ℝ) • realPolynomialEvenPart PRe) +
        (1 / 2 : ℂ) • realPolynomialToComplex ((2 : ℝ) • realPolynomialOddPart PRe) =
        realPolynomialToComplex PRe := by
    ext k
    have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hmod with hmod | hmod <;>
      simp [Polynomial.coeff_add, realPolynomialToComplex,
        realPolynomialEvenPart_coeff, realPolynomialOddPart_coeff, hmod]
  calc
    (1 / 2 : ℂ) • polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialEvenPart PRe)) A +
      (1 / 2 : ℂ) • polynomialOperator
        (realPolynomialToComplex ((2 : ℝ) • realPolynomialOddPart PRe)) A
        = polynomialOperator
            ((1 / 2 : ℂ) • realPolynomialToComplex
                ((2 : ℝ) • realPolynomialEvenPart PRe) +
              (1 / 2 : ℂ) • realPolynomialToComplex
                ((2 : ℝ) • realPolynomialOddPart PRe)) A := by
          rw [polynomialOperator_add, polynomialOperator_smul, polynomialOperator_smul]
    _ = polynomialOperator (realPolynomialToComplex PRe) A := by
          rw [hpoly]

/-- Averaging the doubled even and odd complex coefficient parts reconstructs
`P(A)`.  This is the two-branch bookkeeping needed when the complex
arbitrary-parity QSVT construction realizes complex even/odd branches directly
and then uses one selector ancilla. -/
theorem polynomialOperator_complex_evenOdd_double_average_recompose {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    (1 / 2 : ℂ) • polynomialOperator
        ((2 : ℂ) • complexPolynomialEvenPart P) A +
      (1 / 2 : ℂ) • polynomialOperator
        ((2 : ℂ) • complexPolynomialOddPart P) A =
      polynomialOperator P A := by
  have hpoly :
      (1 / 2 : ℂ) • ((2 : ℂ) • complexPolynomialEvenPart P) +
        (1 / 2 : ℂ) • ((2 : ℂ) • complexPolynomialOddPart P) = P := by
    rw [smul_smul, smul_smul]
    norm_num
    exact complexPolynomial_evenPart_add_oddPart P
  have hoperator := congrArg (fun Q : Polynomial ℂ => polynomialOperator Q A) hpoly
  simpa [polynomialOperator_add, polynomialOperator_smul, smul_smul] using hoperator

/-- The projected block `Π_left U Π_right` used by projected-unitary encodings. -/
def projectedUnitaryBlock {N : Nat} (left right : OrthogonalProjector N)
    (U : Gate (Qubits N)) : HilbertOperator (Qubits N) :=
  left.op * (U : HilbertOperator (Qubits N)) * right.op

/-- The projected block kills vectors in the input-projector complement.  This
is the input-side zero sector used in the source singular-invariant
decomposition [GSLW19, BlockHam.tex:599-611]. -/
theorem projectedUnitaryBlock_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : Gate (Qubits N)}
    {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) psi = psi) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) psi = 0 := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hright_zero :
      HilbertOperator.applyVec right.op psi = 0 :=
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right hpsi
  rw [hright_zero]
  simp [HilbertOperator.applyVec]

/-- The projected block only sees the input's `right`-projector component. -/
theorem projectedUnitaryBlock_applyVec_projector_applyVec {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (psi : StateVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (HilbertOperator.applyVec right.op psi) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U) psi := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hright :
      HilbertOperator.applyVec right.op (HilbertOperator.applyVec right.op psi) =
        HilbertOperator.applyVec right.op psi := by
    rw [← HilbertOperator.mul_applyVec, right.idempotent]
  rw [hright]

/-- The adjoint projected block only sees the output's `left`-projector
component. -/
theorem projectedUnitaryBlock_conjTranspose_applyVec_projector_applyVec {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (psi : StateVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op psi) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose psi := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hleft :
      HilbertOperator.applyVec left.op (HilbertOperator.applyVec left.op psi) =
        HilbertOperator.applyVec left.op psi := by
    rw [← HilbertOperator.mul_applyVec, left.idempotent]
  rw [hleft]

/-- The projected-block Gram operator also kills vectors in the input-projector
complement [GSLW19, BlockHam.tex:599-611]. -/
theorem projectedUnitaryBlock_gram_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : Gate (Qubits N)}
    {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) psi = psi) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U) psi = 0 := by
  rw [HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_applyVec_eq_zero_of_right_complement (left := left)
      (right := right) (U := U) hpsi]
  simp [HilbertOperator.applyVec]

/-- Orthogonal projectors have L2 operator norm at most one.  This elementary
supporting fact is used to bound the singular values in the source
`def:singDec` decomposition [GSLW19, BlockHam.tex:570-613]. -/
theorem orthogonalProjector_norm_le_one {N : Nat} (P : OrthogonalProjector N) :
    ‖P.op‖ ≤ 1 := by
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self P.op
  rw [P.selfAdjoint, P.idempotent] at hnorm
  have hsq : ‖P.op‖ * ‖P.op‖ = ‖P.op‖ := hnorm.symm
  nlinarith [norm_nonneg P.op]

/-- Gates have L2 operator norm one. -/
theorem gate_norm_eq_one {N : Nat} (U : Gate (Qubits N)) :
    ‖(U : HilbertOperator (Qubits N))‖ = 1 :=
  CStarRing.norm_of_mem_unitary U.unitary

/-- Raw finite-register vector norm squared is the real part of its
star-dot-product.  This local bridge keeps the projected-singular-value proof
in matrix notation while using the Hilbert-space norm supplied by Mathlib. -/
theorem stateVector_norm_sq_eq_re_star_dot {N : Nat}
    (v : StateVector (Qubits N)) :
    ‖v‖ ^ 2 = RCLike.re ((star v.ofLp) ⬝ᵥ v.ofLp) := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [← Complex.ofReal_inj]
  simp [Complex.sq_norm, dotProduct, Complex.normSq_apply]

/-- Applying an operator has squared norm `v^* A^* A v`.  This is the Gram
identity used to pass from the spectral theorem for `A^*A` to source singular
values in `def:singDec` [GSLW19, BlockHam.tex:570-613]. -/
theorem applyVec_norm_sq_eq_re_star_dot_gram {N : Nat}
    (A : HilbertOperator (Qubits N)) (v : StateVector (Qubits N)) :
    ‖HilbertOperator.applyVec A v‖ ^ 2 =
      RCLike.re ((star v.ofLp) ⬝ᵥ
        (((A.conjTranspose * A) : HilbertOperator (Qubits N)).mulVec v.ofLp)) := by
  rw [stateVector_norm_sq_eq_re_star_dot (HilbertOperator.applyVec A v)]
  simp only [HilbertOperator.applyVec]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  rw [Matrix.dotProduct_mulVec]

/-- Adjoint transfer for finite-register matrix actions:
`⟪Aψ, Bφ⟫ = ⟪ψ, A†Bφ⟫`.  This is the local Hilbert-space bridge used for the
orthogonal projector decomposition in `lemma:singInvDec` [GSLW19,
BlockHam.tex:570-613]. -/
theorem inner_applyVec_applyVec {N : Nat}
    (A B : HilbertOperator (Qubits N))
    (psi phi : StateVector (Qubits N)) :
    inner ℂ (HilbertOperator.applyVec A psi) (HilbertOperator.applyVec B phi) =
      inner ℂ psi (HilbertOperator.applyVec (A.conjTranspose * B) phi) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, HilbertOperator.applyVec_apply]
  calc ∑ i, (∑ k, B i k * phi k) * starRingEnd ℂ (∑ j, A i j * psi j)
      = ∑ i, ∑ k, ∑ j, (B i k * starRingEnd ℂ (A i j))
          * (phi k * starRingEnd ℂ (psi j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, B i k * starRingEnd ℂ (A i j))
          * (phi k * starRingEnd ℂ (psi j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (A.conjTranspose * B) j k *
          (phi k * starRingEnd ℂ (psi j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (A i j) = starRingEnd ℂ (A i j) from rfl, mul_comm]
    _ = ∑ j, (∑ k, (A.conjTranspose * B) j k * phi k) *
          starRingEnd ℂ (psi j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring

/-- Applying a gate after its adjoint returns the original vector. -/
theorem gate_applyVec_conjTranspose_applyVec {N : Nat}
    (U : Gate (Qubits N)) (psi : StateVector (Qubits N)) :
    U.applyVec (U.conjTranspose.applyVec psi) = psi := by
  change HilbertOperator.applyVec (U : HilbertOperator (Qubits N))
    (HilbertOperator.applyVec (U.conjTranspose : HilbertOperator (Qubits N)) psi) = psi
  rw [← HilbertOperator.mul_applyVec]
  have hUU :
      (U : HilbertOperator (Qubits N)) *
          (U.conjTranspose : HilbertOperator (Qubits N)) =
        1 := by
    change (U : HilbertOperator (Qubits N)) *
          (U : HilbertOperator (Qubits N)).conjTranspose =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.unitary
  rw [hUU, HilbertOperator.one_applyVec]

/-- Applying a gate's adjoint after the gate returns the original vector. -/
theorem gate_conjTranspose_applyVec_applyVec {N : Nat}
    (U : Gate (Qubits N)) (psi : StateVector (Qubits N)) :
    U.conjTranspose.applyVec (U.applyVec psi) = psi := by
  change HilbertOperator.applyVec (U.conjTranspose : HilbertOperator (Qubits N))
    (HilbertOperator.applyVec (U : HilbertOperator (Qubits N)) psi) = psi
  rw [← HilbertOperator.mul_applyVec]
  have hUU :
      (U.conjTranspose : HilbertOperator (Qubits N)) *
          (U : HilbertOperator (Qubits N)) =
        1 := by
    change (U : HilbertOperator (Qubits N)).conjTranspose *
          (U : HilbertOperator (Qubits N)) =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.unitary
  rw [hUU, HilbertOperator.one_applyVec]

/-- Applying a projector complement is subtracting the projector component. -/
theorem orthogonalProjector_complement_applyVec {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N)) :
    HilbertOperator.applyVec (OrthogonalProjector.complement P) psi =
      psi - HilbertOperator.applyVec P.op psi := by
  unfold HilbertOperator.applyVec OrthogonalProjector.complement
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

/-- A vector is the sum of its projector and complementary components. -/
theorem orthogonalProjector_applyVec_add_complement_applyVec {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N)) :
    HilbertOperator.applyVec P.op psi +
        HilbertOperator.applyVec (OrthogonalProjector.complement P) psi = psi := by
  rw [orthogonalProjector_complement_applyVec]
  module

/-- A projector image is orthogonal to its complement. -/
theorem orthogonalProjector_inner_applyVec_complement {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N)) :
    inner ℂ (HilbertOperator.applyVec P.op psi)
      (HilbertOperator.applyVec (OrthogonalProjector.complement P) psi) = 0 := by
  rw [inner_applyVec_applyVec]
  rw [P.selfAdjoint, OrthogonalProjector.mul_complement]
  simp [HilbertOperator.applyVec]

/-- Orthogonal projectors split norm squares into image and complement parts. -/
theorem orthogonalProjector_norm_sq_decomposition {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N)) :
    ‖psi‖ ^ 2 =
      ‖HilbertOperator.applyVec P.op psi‖ ^ 2 +
        ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ ^ 2 := by
  have hsum : P.op + OrthogonalProjector.complement P = (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  have hpsi :
      psi =
        HilbertOperator.applyVec P.op psi +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) psi := by
    calc
      psi = HilbertOperator.applyVec (1 : HilbertOperator (Qubits N)) psi := by
        rw [HilbertOperator.one_applyVec]
      _ = HilbertOperator.applyVec (P.op + OrthogonalProjector.complement P) psi := by
        rw [hsum]
      _ = HilbertOperator.applyVec P.op psi +
            HilbertOperator.applyVec (OrthogonalProjector.complement P) psi := by
        rw [HilbertOperator.add_applyVec]
  calc
    ‖psi‖ ^ 2 =
        ‖HilbertOperator.applyVec P.op psi +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ ^ 2 := by
      exact congrArg (fun x : StateVector (Qubits N) => ‖x‖ ^ 2) hpsi
    _ =
        ‖HilbertOperator.applyVec P.op psi‖ ^ 2 +
          ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (HilbertOperator.applyVec P.op psi)
          (HilbertOperator.applyVec (OrthogonalProjector.complement P) psi)
          (orthogonalProjector_inner_applyVec_complement P psi)

/-- If an orthogonal projector preserves the norm of a unit vector, the vector
already lies in the projector image. -/
theorem orthogonalProjector_applyVec_eq_self_of_norm_eq_one {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N))
    (hpsi : ‖psi‖ = 1)
    (hproj : ‖HilbertOperator.applyVec P.op psi‖ = 1) :
    HilbertOperator.applyVec P.op psi = psi := by
  have hdec := orthogonalProjector_norm_sq_decomposition P psi
  rw [hpsi, hproj] at hdec
  have hcomp_sq :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖]
  have hcomp_norm :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ = 0 := by
    nlinarith [norm_nonneg (HilbertOperator.applyVec (OrthogonalProjector.complement P) psi)]
  have hcomp_zero :
      HilbertOperator.applyVec (OrthogonalProjector.complement P) psi = 0 :=
    norm_eq_zero.mp hcomp_norm
  have hsum : P.op + OrthogonalProjector.complement P = (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  have hdecomp :
      psi =
        HilbertOperator.applyVec P.op psi +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) psi := by
    calc
      psi = HilbertOperator.applyVec (1 : HilbertOperator (Qubits N)) psi := by
        rw [HilbertOperator.one_applyVec]
      _ = HilbertOperator.applyVec (P.op + OrthogonalProjector.complement P) psi := by
        rw [hsum]
      _ = HilbertOperator.applyVec P.op psi +
            HilbertOperator.applyVec (OrthogonalProjector.complement P) psi := by
        rw [HilbertOperator.add_applyVec]
  rw [hcomp_zero, add_zero] at hdecomp
  exact hdecomp.symm

/-- If a unit vector has projector component of norm `σ`, the complementary
projector component has norm `sqrt (1 - σ^2)`.  This is the normalization
identity used for the `0 < σ < 1` two-dimensional sectors in `lemma:singInvDec`
[GSLW19, BlockHam.tex:655-716]. -/
theorem orthogonalProjector_complement_norm_eq_sqrt {N : Nat}
    (P : OrthogonalProjector N) (psi : StateVector (Qubits N)) (sigma : ℝ)
    (hpsi : ‖psi‖ = 1)
    (hproj : ‖HilbertOperator.applyVec P.op psi‖ = sigma) :
    ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ =
      Real.sqrt (1 - sigma ^ 2) := by
  have hdec := orthogonalProjector_norm_sq_decomposition P psi
  have hsq :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) psi‖ ^ 2 =
        1 - sigma ^ 2 := by
    rw [hpsi, hproj] at hdec
    nlinarith
  have hnonneg : 0 ≤ 1 - sigma ^ 2 := by
    rw [← hsq]
    exact sq_nonneg _
  rw [← Real.sq_sqrt hnonneg] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq

/-- Projected-unitary encodings are contractions.  This supplies the upper
singular-value bound used when splitting `def:singDec` into unit, nontrivial,
and kernel sectors [GSLW19, BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_norm_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    ‖projectedUnitaryBlock left right U‖ ≤ 1 := by
  unfold projectedUnitaryBlock
  calc
    ‖left.op * (U : HilbertOperator (Qubits N)) * right.op‖
        ≤ ‖left.op * (U : HilbertOperator (Qubits N))‖ * ‖right.op‖ := by
          exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖left.op‖ * ‖(U : HilbertOperator (Qubits N))‖) * ‖right.op‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
    _ ≤ (1 * 1) * 1 := by
          gcongr
          · exact orthogonalProjector_norm_le_one left
          · exact le_of_eq (gate_norm_eq_one U)
          · exact orthogonalProjector_norm_le_one right
    _ = 1 := by norm_num

/-- The projected block is supported on the left projector. -/
theorem projectedUnitaryBlock_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    left.op * projectedUnitaryBlock left right U =
      projectedUnitaryBlock left right U := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) => A * (U.op * right.op))
    left.idempotent
  simpa [projectedUnitaryBlock, Matrix.mul_assoc] using h

/-- The projected block is supported on the right projector. -/
theorem projectedUnitaryBlock_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    projectedUnitaryBlock left right U * right.op =
      projectedUnitaryBlock left right U := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) => (left.op * U.op) * A)
    right.idempotent
  simpa [projectedUnitaryBlock, Matrix.mul_assoc] using h

/-- The adjoint projected block is supported on the input projector from the
left. -/
theorem projectedUnitaryBlock_conjTranspose_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    right.op * (projectedUnitaryBlock left right U).conjTranspose =
      (projectedUnitaryBlock left right U).conjTranspose := by
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, left.selfAdjoint,
    right.selfAdjoint] using
      congrArg Matrix.conjTranspose
        (projectedUnitaryBlock_right_support left right U)

/-- The adjoint projected block is supported on the output projector from the
right. -/
theorem projectedUnitaryBlock_conjTranspose_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    (projectedUnitaryBlock left right U).conjTranspose * left.op =
      (projectedUnitaryBlock left right U).conjTranspose := by
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, left.selfAdjoint,
    right.selfAdjoint] using
      congrArg Matrix.conjTranspose
        (projectedUnitaryBlock_left_support left right U)

theorem projectedUnitaryBlock_conjTranspose_applyVec_left_supported {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec left.op psi = psi) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose psi =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op psi) := by
  rw [hpsi]

theorem projectedUnitaryBlock_conjTranspose_applyVec_left_support_reduce {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (psi : StateVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op psi) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose psi := by
  rw [← HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_conjTranspose_right_support]

/-- The projected-block Gram operator is supported on the input projector from
the left.  This is the algebraic support fact used when converting the Gram
eigenbasis into the right singular-vector sector of `def:singDec` [GSLW19,
BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_gram_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    right.op *
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U) =
      (projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U := by
  rw [projectedUnitaryBlock]
  simp only [Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      (A * (Matrix.conjTranspose U.op * left.op)) * (left.op * U.op * right.op))
    right.idempotent
  simpa [Matrix.mul_assoc] using h

/-- The projected-block Gram operator is supported on the input projector from
the right. -/
theorem projectedUnitaryBlock_gram_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U) * right.op =
      (projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U := by
  rw [projectedUnitaryBlock]
  simp only [Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      (right.op * (Matrix.conjTranspose U.op * left.op)) * (left.op * U.op * A))
    right.idempotent
  simpa [Matrix.mul_assoc] using h

/-- The Gram operator `A† A` of a projected block is Hermitian.  This is the
Mathlib spectral-theorem entry point for constructing the singular-vector
decomposition used in `lemma:singInvDec` [GSLW19, BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_gram_isHermitian {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self _

/-- The projected-block Gram operator is positive semidefinite, so its spectral
decomposition supplies nonnegative squared singular values [GSLW19,
BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_gram_posSemidef {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The projected-block Gram operator is a contraction. -/
theorem projectedUnitaryBlock_gram_norm_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    ‖(projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U‖ ≤ 1 := by
  have hnorm :=
    Matrix.l2_opNorm_conjTranspose_mul_self (projectedUnitaryBlock left right U)
  have hblock := projectedUnitaryBlock_norm_le_one left right U
  rw [hnorm]
  nlinarith [hblock, norm_nonneg (projectedUnitaryBlock left right U)]

/-- Eigenvalues of the projected-block Gram operator are nonnegative.  These
are the squared singular values used in the SVD invariant-subspace construction
[GSLW19, BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_gram_eigenvalues_nonneg {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    0 ≤ (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i :=
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg
    (projectedUnitaryBlock left right U) i

/-- Gram eigenvalues are at most one, because a projected-unitary block is a
contraction. -/
theorem projectedUnitaryBlock_gram_eigenvalues_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i ≤ 1 := by
  exact (hermitian_eigenvalue_mem_Icc_of_operator_norm_le_one
    ((projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U)
    (projectedUnitaryBlock_gram_isHermitian left right U)
    (projectedUnitaryBlock_gram_norm_le_one left right U) i).2

/-- Orthonormal eigenbasis of the projected-block Gram operator.  This is the
Lean object used to start the SVD-style construction in `def:singDec`
[GSLW19, BlockHam.tex:570-581]. -/
noncomputable def projectedUnitaryBlockGramEigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    OrthonormalBasis (Qubits N).Index ℂ (StateVector (Qubits N)) :=
  (projectedUnitaryBlock_gram_isHermitian left right U).eigenvectorBasis

/-- The output-side Gram operator `A A†` of a projected block.  This is the
adjoint-side spectral object needed for the left-kernel part of
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-611]. -/
def projectedUnitaryBlockLeftGram {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    HilbertOperator (Qubits N) :=
  projectedUnitaryBlock left right U * (projectedUnitaryBlock left right U).conjTranspose

/-- The output-side Gram operator `A A†` is Hermitian. -/
theorem projectedUnitaryBlockLeftGram_isHermitian {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    (projectedUnitaryBlockLeftGram left right U).IsHermitian := by
  simpa [projectedUnitaryBlockLeftGram] using
    Matrix.isHermitian_conjTranspose_mul_self
      ((projectedUnitaryBlock left right U).conjTranspose)

/-- Orthonormal eigenbasis of the output-side Gram operator. -/
noncomputable def projectedUnitaryBlockLeftGramEigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N)) :
    OrthonormalBasis (Qubits N).Index ℂ (StateVector (Qubits N)) :=
  (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvectorBasis

/-- Output-side Gram eigenvector equation. -/
theorem projectedUnitaryBlockLeftGram_mulVec_eigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    Matrix.mulVec (projectedUnitaryBlockLeftGram left right U)
        ⇑(projectedUnitaryBlockLeftGramEigenbasis left right U i) =
      ((projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i : ℂ) •
        ⇑(projectedUnitaryBlockLeftGramEigenbasis left right U i) :=
  (projectedUnitaryBlockLeftGram_isHermitian left right U).mulVec_eigenvectorBasis i

/-- Norm-square bridge for applying `A†` to an output-side Gram eigenvector. -/
theorem projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_norm_sq
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    ‖HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (projectedUnitaryBlockLeftGramEigenbasis left right U i)‖ ^ 2 =
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i := by
  rw [applyVec_norm_sq_eq_re_star_dot_gram]
  have hgram := projectedUnitaryBlockLeftGram_mulVec_eigenbasis left right U i
  have hgram_target :
      (((projectedUnitaryBlock left right U).conjTranspose).conjTranspose *
            (projectedUnitaryBlock left right U).conjTranspose).mulVec
          ((projectedUnitaryBlockLeftGramEigenbasis left right U i).ofLp) =
        ((projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i : ℂ) •
          ((projectedUnitaryBlockLeftGramEigenbasis left right U i).ofLp) := by
    simpa [projectedUnitaryBlockLeftGram] using hgram
  rw [hgram_target]
  have hdot :
      (star (projectedUnitaryBlockLeftGramEigenbasis left right U i).ofLp) ⬝ᵥ
          (projectedUnitaryBlockLeftGramEigenbasis left right U i).ofLp = 1 := by
    have hnorm :=
      (projectedUnitaryBlockLeftGramEigenbasis left right U).orthonormal.norm_eq_one i
    have hinner :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
        (projectedUnitaryBlockLeftGramEigenbasis left right U i)
    rw [EuclideanSpace.inner_eq_star_dotProduct, hnorm] at hinner
    norm_num at hinner
    simpa [dotProduct_comm] using hinner
  rw [dotProduct_smul, hdot, smul_eq_mul, mul_one]
  exact Complex.ofReal_re
    ((projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i)

/-- A zero output-side Gram eigenvalue gives a left-kernel vector for the
adjoint projected block. -/
theorem projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_eq_zero_of_eigenvalue_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i = 0) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (projectedUnitaryBlockLeftGramEigenbasis left right U i) = 0 := by
  have hnorm_sq :=
    projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_norm_sq
      left right U i
  rw [hlambda] at hnorm_sq
  have hnorm :
      ‖HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (projectedUnitaryBlockLeftGramEigenbasis left right U i)‖ = 0 := by
    nlinarith [norm_nonneg
      (HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (projectedUnitaryBlockLeftGramEigenbasis left right U i))]
  exact norm_eq_zero.mp hnorm

/-- Gram eigenvectors are normalized by the spectral theorem's orthonormal
basis. -/
theorem projectedUnitaryBlockGramEigenbasis_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    ‖(projectedUnitaryBlockGramEigenbasis left right U i :
      StateVector (Qubits N))‖ = 1 :=
  (projectedUnitaryBlockGramEigenbasis left right U).orthonormal.norm_eq_one i

/-- Eigenvector equation for the projected-block Gram eigenbasis. -/
theorem projectedUnitaryBlock_gram_mulVec_eigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    Matrix.mulVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        ⇑(projectedUnitaryBlockGramEigenbasis left right U i) =
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) •
        ⇑(projectedUnitaryBlockGramEigenbasis left right U i) :=
  (projectedUnitaryBlock_gram_isHermitian left right U).mulVec_eigenvectorBasis i

/-- A nonzero Gram eigenvector lies in the input projector image.  This is the
first support step in extracting the right singular-vector sector of
`def:singDec` from the spectral theorem [GSLW19, BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    Matrix.mulVec right.op
        ⇑(projectedUnitaryBlockGramEigenbasis left right U i) =
      ⇑(projectedUnitaryBlockGramEigenbasis left right U i) := by
  let G :=
    (projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U
  let v := ⇑(projectedUnitaryBlockGramEigenbasis left right U i)
  let lambda : ℂ :=
    (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i
  have hev : Matrix.mulVec G v = lambda • v := by
    dsimp [G, v, lambda]
    exact projectedUnitaryBlock_gram_mulVec_eigenbasis left right U i
  have hsupport : right.op * G = G := by
    dsimp [G]
    exact projectedUnitaryBlock_gram_left_support left right U
  have hleft : Matrix.mulVec right.op (Matrix.mulVec G v) = Matrix.mulVec G v := by
    have hmat := congrArg (fun M : HilbertOperator (Qubits N) => Matrix.mulVec M v)
      hsupport
    simpa [Matrix.mulVec_mulVec] using hmat
  have hright :
      Matrix.mulVec right.op (lambda • v) = lambda • Matrix.mulVec right.op v := by
    rw [Matrix.mulVec_smul]
  have h := congrArg (fun w => Matrix.mulVec right.op w) hev
  rw [hleft, hright] at h
  rw [hev] at h
  have hcancel := congrArg (fun w => lambda⁻¹ • w) h.symm
  have hmul : lambda⁻¹ * lambda = 1 := inv_mul_cancel₀ hlambda
  simpa [smul_smul, hmul] using hcancel

/-- State-vector form of
`projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero`. -/
theorem projectedUnitaryBlockGramEigenbasis_right_applyVec_support_of_eigenvalue_ne_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec right.op
        (projectedUnitaryBlockGramEigenbasis left right U i : StateVector (Qubits N)) =
      (projectedUnitaryBlockGramEigenbasis left right U i : StateVector (Qubits N)) := by
  ext j
  simpa [HilbertOperator.applyVec_apply, Matrix.mulVec, dotProduct] using
    congrFun
      (projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero
        left right U i hlambda) j

/-- Singular values induced by the projected-block Gram spectrum. -/
noncomputable def projectedUnitaryBlockSingularValue {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) : ℝ :=
  Real.sqrt ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i)

theorem projectedUnitaryBlockSingularValue_nonneg {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    0 ≤ projectedUnitaryBlockSingularValue left right U i :=
  Real.sqrt_nonneg _

theorem projectedUnitaryBlockSingularValue_sq {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    (projectedUnitaryBlockSingularValue left right U i) ^ 2 =
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i := by
  rw [projectedUnitaryBlockSingularValue, Real.sq_sqrt]
  exact projectedUnitaryBlock_gram_eigenvalues_nonneg left right U i

/-- Singular values of a projected-unitary block lie in `[0,1]`, matching the
source sector parameter `σ` in `lemma:singInvDec` [GSLW19,
BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlockSingularValue_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    projectedUnitaryBlockSingularValue left right U i ≤ 1 := by
  rw [projectedUnitaryBlockSingularValue, Real.sqrt_le_one]
  exact projectedUnitaryBlock_gram_eigenvalues_le_one left right U i

/-- A nonzero Gram eigenvalue gives a nonzero singular value. -/
theorem projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    (projectedUnitaryBlockSingularValue left right U i : ℂ) ≠ 0 := by
  intro hsigma
  have hsigma_real : projectedUnitaryBlockSingularValue left right U i = 0 :=
    Complex.ofReal_eq_zero.mp hsigma
  have hsq := projectedUnitaryBlockSingularValue_sq left right U i
  have hlambda_real :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0 := by
    rw [← hsq, hsigma_real]
    norm_num
  exact hlambda (by exact_mod_cast hlambda_real)

/-- Right singular-vector candidate obtained from the Gram eigenbasis. -/
noncomputable def projectedUnitaryBlockRightSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) : StateVector (Qubits N) :=
  projectedUnitaryBlockGramEigenbasis left right U i

/-- Right singular-vector candidates are normalized. -/
theorem projectedUnitaryBlockRightSingularVector_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    ‖projectedUnitaryBlockRightSingularVector left right U i‖ = 1 := by
  simp [projectedUnitaryBlockRightSingularVector,
    projectedUnitaryBlockGramEigenbasis_norm_eq_one left right U i]

/-- Left singular-vector candidate `σ⁻¹ A ψ` for nonzero singular-value
sectors.  The nonzero hypothesis is carried by the theorems using this
definition, keeping the definition total. -/
noncomputable def projectedUnitaryBlockLeftSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) : StateVector (Qubits N) :=
  ((projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹) •
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
      (projectedUnitaryBlockRightSingularVector left right U i)

theorem projectedUnitaryBlockRightSingularVector_support_of_eigenvalue_ne_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec right.op
        (projectedUnitaryBlockRightSingularVector left right U i) =
      projectedUnitaryBlockRightSingularVector left right U i := by
  simpa [projectedUnitaryBlockRightSingularVector] using
    projectedUnitaryBlockGramEigenbasis_right_applyVec_support_of_eigenvalue_ne_zero
      left right U i hlambda

theorem projectedUnitaryBlockLeftSingularVector_support {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    HilbertOperator.applyVec left.op
        (projectedUnitaryBlockLeftSingularVector left right U i) =
      projectedUnitaryBlockLeftSingularVector left right U i := by
  unfold projectedUnitaryBlockLeftSingularVector
  rw [HilbertOperator.applyVec_smul]
  congr 1
  rw [← HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_left_support]

theorem projectedUnitaryBlock_applyVec_rightSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hsigma : (projectedUnitaryBlockSingularValue left right U i : ℂ) ≠ 0) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i) =
      (projectedUnitaryBlockSingularValue left right U i : ℂ) •
        projectedUnitaryBlockLeftSingularVector left right U i := by
  unfold projectedUnitaryBlockLeftSingularVector
  rw [smul_smul]
  have hmul :
      (projectedUnitaryBlockSingularValue left right U i : ℂ) *
          (projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ hsigma
  simp [hmul]

theorem projectedUnitaryBlock_gram_applyVec_rightSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i) =
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) •
        projectedUnitaryBlockRightSingularVector left right U i := by
  ext j
  simpa [HilbertOperator.applyVec_apply, Matrix.mulVec, dotProduct,
    projectedUnitaryBlockRightSingularVector] using
    congrFun (projectedUnitaryBlock_gram_mulVec_eigenbasis left right U i) j

/-- Applying the projected block to a right singular vector has squared norm
`σ^2`.  This is the norm bridge used to turn the Gram eigenvector into the
source singular-pair normalization in `def:singDec` [GSLW19,
BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlock_applyVec_rightSingularVector_norm_sq {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index) :
    ‖HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i)‖ ^ 2 =
      (projectedUnitaryBlockSingularValue left right U i) ^ 2 := by
  rw [applyVec_norm_sq_eq_re_star_dot_gram]
  have hgram := projectedUnitaryBlock_gram_applyVec_rightSingularVector left right U i
  have hgram_raw := congrArg WithLp.ofLp hgram
  simp only [HilbertOperator.applyVec, WithLp.ofLp_toLp] at hgram_raw
  rw [hgram_raw]
  rw [← projectedUnitaryBlockSingularValue_sq left right U i]
  have hdot :
      (star (projectedUnitaryBlockRightSingularVector left right U i).ofLp) ⬝ᵥ
          (projectedUnitaryBlockRightSingularVector left right U i).ofLp = 1 := by
    have hnorm := projectedUnitaryBlockRightSingularVector_norm_eq_one left right U i
    have hinner :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
        (projectedUnitaryBlockRightSingularVector left right U i)
    rw [EuclideanSpace.inner_eq_star_dotProduct, hnorm] at hinner
    norm_num at hinner
    simpa [dotProduct_comm] using hinner
  change RCLike.re
      ((star (projectedUnitaryBlockRightSingularVector left right U i).ofLp) ⬝ᵥ
        (((projectedUnitaryBlockSingularValue left right U i ^ 2 : ℝ) : ℂ) •
          (projectedUnitaryBlockRightSingularVector left right U i).ofLp)) =
    projectedUnitaryBlockSingularValue left right U i ^ 2
  rw [dotProduct_smul, hdot, smul_eq_mul, mul_one]
  exact Complex.ofReal_re ((projectedUnitaryBlockSingularValue left right U i) ^ 2)

/-- A zero Gram eigenvalue gives a right-kernel vector for the projected block.
This is the entry point for the zero-singular-value part of
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-611]. -/
theorem projectedUnitaryBlock_applyVec_rightSingularVector_eq_zero_of_eigenvalue_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i = 0) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i) = 0 := by
  have hnorm_sq :=
    projectedUnitaryBlock_applyVec_rightSingularVector_norm_sq left right U i
  have hsigma_sq :
      (projectedUnitaryBlockSingularValue left right U i) ^ 2 = 0 := by
    rw [projectedUnitaryBlockSingularValue_sq, hlambda]
  rw [hsigma_sq] at hnorm_sq
  have hnorm :
      ‖HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i)‖ = 0 := by
    nlinarith [norm_nonneg
      (HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i))]
  exact norm_eq_zero.mp hnorm

/-- The nonzero left singular-vector candidate is normalized.  This completes
the source singular-pair data obtained from the Gram eigenbasis before the
`σ=1`/`0<σ<1` sector split [GSLW19, BlockHam.tex:570-613]. -/
theorem projectedUnitaryBlockLeftSingularVector_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hsigma : (projectedUnitaryBlockSingularValue left right U i : ℂ) ≠ 0) :
    ‖projectedUnitaryBlockLeftSingularVector left right U i‖ = 1 := by
  unfold projectedUnitaryBlockLeftSingularVector
  rw [norm_smul]
  have hsigma_real_ne : projectedUnitaryBlockSingularValue left right U i ≠ 0 := by
    intro hzero
    exact hsigma (by exact_mod_cast hzero)
  have hnormA_sq :=
    projectedUnitaryBlock_applyVec_rightSingularVector_norm_sq left right U i
  have hnormA :
      ‖HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (projectedUnitaryBlockRightSingularVector left right U i)‖ =
        projectedUnitaryBlockSingularValue left right U i := by
    exact (sq_eq_sq₀ (norm_nonneg _)
      (projectedUnitaryBlockSingularValue_nonneg left right U i)).mp hnormA_sq
  rw [hnormA, norm_inv, Complex.norm_of_nonneg
    (projectedUnitaryBlockSingularValue_nonneg left right U i)]
  field_simp [hsigma_real_ne]

theorem projectedUnitaryBlock_conjTranspose_applyVec_leftSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hsigma : (projectedUnitaryBlockSingularValue left right U i : ℂ) ≠ 0) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (projectedUnitaryBlockLeftSingularVector left right U i) =
      (projectedUnitaryBlockSingularValue left right U i : ℂ) •
        projectedUnitaryBlockRightSingularVector left right U i := by
  unfold projectedUnitaryBlockLeftSingularVector
  rw [HilbertOperator.applyVec_smul, ← HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_gram_applyVec_rightSingularVector]
  rw [smul_smul]
  have hsq :
      (((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℝ) : ℂ) =
        (projectedUnitaryBlockSingularValue left right U i : ℂ) ^ 2 := by
    exact_mod_cast (projectedUnitaryBlockSingularValue_sq left right U i).symm
  have hscalar :
      (projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹ *
          ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) =
        (projectedUnitaryBlockSingularValue left right U i : ℂ) := by
    rw [hsq, pow_two]
    calc
      (projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹ *
          ((projectedUnitaryBlockSingularValue left right U i : ℂ) *
            (projectedUnitaryBlockSingularValue left right U i : ℂ)) =
          ((projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹ *
            (projectedUnitaryBlockSingularValue left right U i : ℂ)) *
            (projectedUnitaryBlockSingularValue left right U i : ℂ) := by
        ring
      _ = (1 : ℂ) *
            (projectedUnitaryBlockSingularValue left right U i : ℂ) := by
        rw [inv_mul_cancel₀ hsigma]
      _ = (projectedUnitaryBlockSingularValue left right U i : ℂ) := by
        simp
  rw [hscalar]

/-- Source-facing nonzero singular-vector pair for the projected block `A`.
This is the part of `def:singDec` obtained from the Gram spectral theorem before
constructing the orthogonal complement vectors used in `lemma:singInvDec`
[GSLW19, BlockHam.tex:570-613]. -/
structure SourceNonzeroSingularPair {N : Nat} (A : HilbertOperator (Qubits N))
    (left right : OrthogonalProjector N) where
  /-- Nonzero singular value for the projected block. -/
  sigma : ℝ
  sigma_pos : 0 < sigma
  /-- Unit right singular vector supported by the input projector. -/
  rightVec : StateVector (Qubits N)
  /-- Unit left singular vector supported by the output projector. -/
  leftVec : StateVector (Qubits N)
  right_norm : ‖rightVec‖ = 1
  left_norm : ‖leftVec‖ = 1
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  A_right :
    HilbertOperator.applyVec A rightVec = (sigma : ℂ) • leftVec
  Astar_left :
    HilbertOperator.applyVec A.conjTranspose leftVec = (sigma : ℂ) • rightVec

/-- Build the nonzero singular-vector pair attached to a nonzero Gram
eigenvalue.  The remaining `lemma:singInvDec` work is to split these pairs into
the `sigma=1` and `0<sigma<1` sectors and construct the source complement
vectors [GSLW19, BlockHam.tex:583-613,718-735]. -/
noncomputable def projectedUnitaryBlockNonzeroSingularPair {N : Nat}
    (left right : OrthogonalProjector N) (U : Gate (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceNonzeroSingularPair (projectedUnitaryBlock left right U) left right where
  sigma := projectedUnitaryBlockSingularValue left right U i
  sigma_pos := by
    have hsigma : (projectedUnitaryBlockSingularValue left right U i : ℂ) ≠ 0 :=
      projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero
        left right U i hlambda
    have hsigma_real : projectedUnitaryBlockSingularValue left right U i ≠ 0 := by
      intro hzero
      exact hsigma (by exact_mod_cast hzero)
    exact lt_of_le_of_ne
      (projectedUnitaryBlockSingularValue_nonneg left right U i)
      (Ne.symm hsigma_real)
  rightVec := projectedUnitaryBlockRightSingularVector left right U i
  leftVec := projectedUnitaryBlockLeftSingularVector left right U i
  right_norm := projectedUnitaryBlockRightSingularVector_norm_eq_one left right U i
  left_norm :=
    projectedUnitaryBlockLeftSingularVector_norm_eq_one left right U i
      (projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero
        left right U i hlambda)
  right_support :=
    projectedUnitaryBlockRightSingularVector_support_of_eigenvalue_ne_zero
      left right U i hlambda
  left_support := projectedUnitaryBlockLeftSingularVector_support left right U i
  A_right :=
    projectedUnitaryBlock_applyVec_rightSingularVector left right U i
      (projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero
        left right U i hlambda)
  Astar_left :=
    projectedUnitaryBlock_conjTranspose_applyVec_leftSingularVector left right U i
      (projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero
        left right U i hlambda)

namespace SourceNonzeroSingularPair

/-- A nonzero singular pair for a projected-unitary block has `σ ∈ (0,1]`.
This is the sector split used in `def:singDec` before separating the
`σ=1` and `0<σ<1` blocks [GSLW19, BlockHam.tex:583-613]. -/
theorem sigma_mem_Ioc {N : Nat} {left right : OrthogonalProjector N}
    {U : Gate (Qubits N)} {i : (Qubits N).Index}
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma ∈
      Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma_pos
  · exact projectedUnitaryBlockSingularValue_le_one left right U i

/-- The source singular-pair sector split: a nonzero singular value is either
the unit sector or the genuine two-dimensional sector. -/
theorem sigma_eq_one_or_lt_one {N : Nat} {left right : OrthogonalProjector N}
    {U : Gate (Qubits N)} {i : (Qubits N).Index}
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma = 1 ∨
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma < 1 := by
  have hle := (sigma_mem_Ioc (left := left) (right := right) (U := U)
    (i := i) hlambda).2
  exact eq_or_lt_of_le hle

end SourceNonzeroSingularPair

/-- The even-parity singular-value polynomial target from the source
definition of `P^{(SV)}`: if `P(X) = R(X^2)`, the even transform acts on the
input projector side.  The projector factors are essential: for `P = 1`, the
target is the identity on `Π`, not on the whole ambient Hilbert space [GSLW19,
BlockHam.tex:747-764]. -/
noncomputable def evenSingularValuePolynomial {N : Nat}
    (input : OrthogonalProjector N) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  input.op * polynomialOperator (evenSquareQuotient P) (A.conjTranspose * A) * input.op

/-- The odd-parity singular-value polynomial target from the source definition
of `P^{(SV)}`: if `P(X) = X R(X^2)`, the odd transform is
`A R(A^* A)` [GSLW19, BlockHam.tex:747-764]. -/
noncomputable def oddSingularValuePolynomial {N : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  A * polynomialOperator (oddSquareQuotient P) (A.conjTranspose * A)

/-- Parity-selected singular-value polynomial target `P^{(SV)}(A)`.  Even
degree uses the input-side projector target; odd degree maps from the input
projector side to the output projector side [GSLW19, BlockHam.tex:747-764]. -/
noncomputable def singularValuePolynomial {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    HilbertOperator (Qubits N) :=
  if L % 2 = 0 then
    evenSingularValuePolynomial input P A
  else
    oddSingularValuePolynomial P A

/-- The even branch of `P^{(SV)}` kills the input-projector complement because
the target contains the input projector on the right. -/
theorem evenSingularValuePolynomial_applyVec_eq_zero_of_input_complement {N : Nat}
    {input : OrthogonalProjector N} {A : HilbertOperator (Qubits N)}
    (P : Polynomial ℂ) {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement input) psi = psi) :
    HilbertOperator.applyVec (evenSingularValuePolynomial input P A) psi = 0 := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hinput_zero :
      HilbertOperator.applyVec input.op psi = 0 :=
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      input hpsi
  rw [hinput_zero]
  simp [HilbertOperator.applyVec]

/-- The odd branch of `P^{(SV)}` kills the input-projector complement for a
projected unitary block: the Gram operator has eigenvalue `0` there, and the
leading projected block kills the remaining scalar multiple. -/
theorem oddSingularValuePolynomial_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : Gate (Qubits N)}
    (P : Polynomial ℂ) {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) psi = psi) :
    HilbertOperator.applyVec
        (oddSingularValuePolynomial P (projectedUnitaryBlock left right U)) psi = 0 := by
  have hgram :
      HilbertOperator.applyVec
          ((projectedUnitaryBlock left right U).conjTranspose *
            projectedUnitaryBlock left right U) psi =
        (0 : ℂ) • psi := by
    rw [zero_smul]
    exact projectedUnitaryBlock_gram_applyVec_eq_zero_of_right_complement
      (left := left) (right := right) (U := U) hpsi
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U) 0 psi hgram,
    HilbertOperator.applyVec_smul,
    projectedUnitaryBlock_applyVec_eq_zero_of_right_complement (left := left)
      (right := right) (U := U) hpsi]
  simp

/-- The parity-selected singular-value polynomial target kills vectors in the
input-projector complement for projected-unitary encodings. -/
theorem singularValuePolynomial_applyVec_eq_zero_of_right_complement {N L : Nat}
    {left right : OrthogonalProjector N} {U : Gate (Qubits N)}
    (P : Polynomial ℂ) {psi : StateVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) psi = psi) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U)) psi = 0 := by
  unfold singularValuePolynomial
  by_cases hL : L % 2 = 0
  · simp [hL, evenSingularValuePolynomial_applyVec_eq_zero_of_input_complement
      P hpsi]
  · simp [hL, oddSingularValuePolynomial_applyVec_eq_zero_of_right_complement
      (left := left) (right := right) (U := U) P hpsi]

@[simp]
theorem singularValuePolynomial_X_one {N : Nat} (input : OrthogonalProjector N)
    (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input 1 (Polynomial.X : Polynomial ℂ) A = A := by
  unfold singularValuePolynomial oddSingularValuePolynomial polynomialOperator
  simp

theorem evenSingularValuePolynomial_add {N : Nat} (input : OrthogonalProjector N)
    (P Q : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    evenSingularValuePolynomial input (P + Q) A =
      evenSingularValuePolynomial input P A + evenSingularValuePolynomial input Q A := by
  unfold evenSingularValuePolynomial
  rw [evenSquareQuotient_add, polynomialOperator_add]
  simp [Matrix.mul_add, Matrix.add_mul]

theorem evenSingularValuePolynomial_smul {N : Nat} (input : OrthogonalProjector N)
    (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    evenSingularValuePolynomial input (c • P) A =
      c • evenSingularValuePolynomial input P A := by
  unfold evenSingularValuePolynomial
  rw [evenSquareQuotient_smul, polynomialOperator_smul]
  simp

theorem oddSingularValuePolynomial_add {N : Nat} (P Q : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) :
    oddSingularValuePolynomial (P + Q) A =
      oddSingularValuePolynomial P A + oddSingularValuePolynomial Q A := by
  unfold oddSingularValuePolynomial
  rw [oddSquareQuotient_add, polynomialOperator_add]
  simp [Matrix.mul_add]

theorem oddSingularValuePolynomial_smul {N : Nat}
    (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    oddSingularValuePolynomial (c • P) A =
      c • oddSingularValuePolynomial P A := by
  unfold oddSingularValuePolynomial
  rw [oddSquareQuotient_smul, polynomialOperator_smul]
  simp

theorem singularValuePolynomial_add {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (P Q : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input L (P + Q) A =
      singularValuePolynomial input L P A + singularValuePolynomial input L Q A := by
  unfold singularValuePolynomial
  by_cases h : L % 2 = 0
  · simp [h, evenSingularValuePolynomial_add]
  · simp [h, oddSingularValuePolynomial_add]

theorem singularValuePolynomial_smul {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input L (c • P) A =
      c • singularValuePolynomial input L P A := by
  unfold singularValuePolynomial
  by_cases h : L % 2 = 0
  · simp [h, evenSingularValuePolynomial_smul]
  · simp [h, oddSingularValuePolynomial_smul]

/-- Polynomial average identities lift through the singular-value polynomial
operation used in `cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
theorem singularValuePolynomial_average_of_polynomial_average {N : Nat}
    (input : OrthogonalProjector N) (L : ℕ)
    (P Pneg Preal : Polynomial ℂ) (A : HilbertOperator (Qubits N))
    (havg : (1 / 2 : ℂ) • P + (1 / 2 : ℂ) • Pneg = Preal) :
    (1 / 2 : ℂ) • singularValuePolynomial input L P A +
        (1 / 2 : ℂ) • singularValuePolynomial input L Pneg A =
      singularValuePolynomial input L Preal A := by
  rw [← havg, singularValuePolynomial_add, singularValuePolynomial_smul,
    singularValuePolynomial_smul]

/-- On a nonzero singular pair, the Gram operator `A^* A` has eigenvalue
`sigma^2` on the right singular vector.  This is the target-side scalar
calculation used in the local blocks of the singular-value transform
[GSLW19, BlockHam.tex:747-849]. -/
theorem singularPair_gram_applyVec_rightVec {N : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right) :
    HilbertOperator.applyVec (A.conjTranspose * A) pair.rightVec =
      ((pair.sigma : Complex) ^ 2) • pair.rightVec := by
  rw [HilbertOperator.mul_applyVec, pair.A_right, HilbertOperator.applyVec_smul,
    pair.Astar_left, smul_smul]
  ring_nf

/-- Even branch of `P^{(SV)}` on a right singular vector: the quotient
polynomial evaluates at `sigma^2`, hence the full target scalar is `P(sigma)`
[GSLW19, BlockHam.tex:747-764]. -/
theorem evenSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec (evenSingularValuePolynomial right P A) pair.rightVec =
      P.eval (pair.sigma : Complex) • pair.rightVec := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, pair.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      (A.conjTranspose * A) ((pair.sigma : Complex) ^ 2) pair.rightVec
      (singularPair_gram_applyVec_rightVec pair),
    evenSquareQuotient_eval_sq_of_hasParity hL hP,
    HilbertOperator.applyVec_smul, pair.right_support]

/-- Odd branch of `P^{(SV)}` on a right singular vector: after applying the
quotient polynomial to `A^*A`, the leading `A` maps to the left singular vector
and contributes the missing factor `sigma` [GSLW19, BlockHam.tex:747-764]. -/
theorem oddSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec (oddSingularValuePolynomial P A) pair.rightVec =
      P.eval (pair.sigma : Complex) • pair.leftVec := by
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      (A.conjTranspose * A) ((pair.sigma : Complex) ^ 2) pair.rightVec
      (singularPair_gram_applyVec_rightVec pair),
    HilbertOperator.applyVec_smul, pair.A_right, smul_smul]
  have hodd := oddSquareQuotient_eval_sq_of_hasParity hL hP (pair.sigma : Complex)
  rw [← hodd]
  ring_nf

/-- Even-parity branch of the parity-selected singular-value target on a
right singular vector [GSLW19, BlockHam.tex:747-764]. -/
theorem singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec (singularValuePolynomial right L P A) pair.rightVec =
      P.eval (pair.sigma : Complex) • pair.rightVec := by
  unfold singularValuePolynomial
  simp [hL, evenSingularValuePolynomial_applyVec_rightVec pair P hL hP]

/-- Odd-parity branch of the parity-selected singular-value target on a right
singular vector [GSLW19, BlockHam.tex:747-764]. -/
theorem singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec (singularValuePolynomial right L P A) pair.rightVec =
      P.eval (pair.sigma : Complex) • pair.leftVec := by
  unfold singularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  simp [hnot, oddSingularValuePolynomial_applyVec_rightVec pair P hL hP]

/-- A projected-unitary encoding of a full-space operator by a unitary gate and
two orthogonal projectors.  Ordinary block encodings are the special case where
both projectors select the all-zero ancilla block. -/
structure ProjectedUnitaryEncoding {N : Nat} (left right : OrthogonalProjector N)
    (U : Gate (Qubits N)) (A : HilbertOperator (Qubits N)) : Prop where
  block_eq : projectedUnitaryBlock left right U = A

theorem ProjectedUnitaryEncoding.block_entry {N : Nat}
    {left right : OrthogonalProjector N} {U : Gate (Qubits N)} {A : HilbertOperator (Qubits N)}
    (h : ProjectedUnitaryEncoding left right U A) (i j : Fin (2 ^ N)) :
    projectedUnitaryBlock left right U i j = A i j := by
  rw [h.block_eq]

/-- Embed a system operator into the `|0^a>` ancilla block of the joint
ancilla-system space, with zero action outside that block. -/
def zeroAncillaEmbeddedOperator (a n : Nat) (A : HilbertOperator (Qubits n)) :
    HilbertOperator (Qubits (a + n)) :=
  fun i j =>
    if (prodEquiv.symm i).1 = 0 then
      if (prodEquiv.symm j).1 = 0 then
        A (prodEquiv.symm i).2 (prodEquiv.symm j).2
      else 0
    else 0

/-- The top-left block of a zero-ancilla embedding is the embedded system
operator. -/
@[simp]
theorem projectedBlock_zeroAncillaEmbeddedOperator {a n : Nat}
    (A : HilbertOperator (Qubits n)) :
    projectedBlock a n (zeroAncillaEmbeddedOperator a n A) = A := by
  ext i j
  simp [projectedBlock, zeroAncillaEmbeddedOperator]

/-- Multiplication is preserved inside the zero-ancilla embedded block. -/
theorem zeroAncillaEmbeddedOperator_mul {a n : Nat}
    (A B : HilbertOperator (Qubits n)) :
    zeroAncillaEmbeddedOperator a n A * zeroAncillaEmbeddedOperator a n B =
      zeroAncillaEmbeddedOperator a n (A * B) := by
  ext i j
  rcases (prodEquiv (m := a) (n := n)).surjective i with ⟨⟨x, y⟩, rfl⟩
  rcases (prodEquiv (m := a) (n := n)).surjective j with ⟨⟨x', y'⟩, rfl⟩
  by_cases hx : x = 0
  · by_cases hx' : x' = 0
    · simp only [Matrix.mul_apply]
      rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
      simp [zeroAncillaEmbeddedOperator, hx, hx', Fintype.sum_prod_type,
        Matrix.mul_apply]
    · simp [zeroAncillaEmbeddedOperator, hx, hx', Matrix.mul_apply,
        ← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  · simp [zeroAncillaEmbeddedOperator, hx, Matrix.mul_apply,
      ← Equiv.sum_comp (prodEquiv (m := a) (n := n))]

/-- Positive powers of a zero-ancilla embedded operator remain zero-ancilla
embeddings of the corresponding system powers. -/
theorem zeroAncillaEmbeddedOperator_pow_succ {a n : Nat}
    (A : HilbertOperator (Qubits n)) (k : Nat) :
    zeroAncillaEmbeddedOperator a n A ^ (k + 1) =
      zeroAncillaEmbeddedOperator a n (A ^ (k + 1)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        zeroAncillaEmbeddedOperator a n A ^ (k + 1 + 1) =
            zeroAncillaEmbeddedOperator a n A ^ (k + 1) *
              zeroAncillaEmbeddedOperator a n A := by
          rw [pow_succ]
        _ = zeroAncillaEmbeddedOperator a n (A ^ (k + 1)) *
              zeroAncillaEmbeddedOperator a n A := by
          rw [ih]
        _ = zeroAncillaEmbeddedOperator a n (A ^ (k + 1) * A) := by
          rw [zeroAncillaEmbeddedOperator_mul]
        _ = zeroAncillaEmbeddedOperator a n (A ^ (k + 1 + 1)) := by
          exact congrArg (zeroAncillaEmbeddedOperator a n)
            (pow_succ A (k + 1)).symm

/-- Taking the top-left block commutes with powers of a zero-ancilla embedded
operator. -/
theorem projectedBlock_zeroAncillaEmbeddedOperator_pow {a n : Nat}
    (A : HilbertOperator (Qubits n)) (k : Nat) :
    projectedBlock a n (zeroAncillaEmbeddedOperator a n A ^ k) = A ^ k := by
  cases k with
  | zero =>
      ext i j
      by_cases hij : i = j <;> simp [projectedBlock, hij]
  | succ k =>
      rw [zeroAncillaEmbeddedOperator_pow_succ, projectedBlock_zeroAncillaEmbeddedOperator]

/-- The top-left block of `zeroAncillaEmbeddedOperator A * M` is `A` times the
top-left block of `M`. -/
theorem projectedBlock_zeroAncillaEmbeddedOperator_mul_left {a n : Nat}
    (A : HilbertOperator (Qubits n)) (M : HilbertOperator (Qubits (a + n))) :
    projectedBlock a n (zeroAncillaEmbeddedOperator a n A * M) =
      A * projectedBlock a n M := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [zeroAncillaEmbeddedOperator, Fintype.sum_prod_type]

/-- The top-left block of `M * zeroAncillaEmbeddedOperator A` is the top-left
block of `M` times `A`. -/
theorem projectedBlock_mul_zeroAncillaEmbeddedOperator_right {a n : Nat}
    (M : HilbertOperator (Qubits (a + n))) (A : HilbertOperator (Qubits n)) :
    projectedBlock a n (M * zeroAncillaEmbeddedOperator a n A) =
      projectedBlock a n M * A := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [zeroAncillaEmbeddedOperator, Fintype.sum_prod_type]

/-- The top-left block of a polynomial in a zero-ancilla embedded operator is
the corresponding polynomial in the system operator. -/
theorem projectedBlock_polynomialOperator_zeroAncillaEmbeddedOperator {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    projectedBlock a n (polynomialOperator P (zeroAncillaEmbeddedOperator a n A)) =
      polynomialOperator P A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [polynomialOperator_add, polynomialOperator_add]
      ext i j
      change (projectedBlock a n (polynomialOperator p (zeroAncillaEmbeddedOperator a n A))) i j +
          (projectedBlock a n (polynomialOperator q (zeroAncillaEmbeddedOperator a n A))) i j =
        (polynomialOperator p A) i j + (polynomialOperator q A) i j
      rw [hp, hq]
  | monomial k c =>
      unfold polynomialOperator
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      ext i j
      have hpow :=
        congrArg (fun M : HilbertOperator (Qubits n) => M i j)
          (projectedBlock_zeroAncillaEmbeddedOperator_pow (a := a) (n := n) A k)
      change
        (projectedBlock a n
          ((algebraMap ℂ (HilbertOperator (Qubits (a + n)))) c *
            zeroAncillaEmbeddedOperator a n A ^ k)) i j =
          (((algebraMap ℂ (HilbertOperator (Qubits n))) c) * A ^ k) i j
      simpa [projectedBlock, Matrix.mul_apply, Matrix.algebraMap_matrix_apply]
        using congrArg (fun z => c * z) hpow

/-- Conjugate-transpose preserves the zero-ancilla embedding. -/
theorem zeroAncillaEmbeddedOperator_conjTranspose {a n : Nat}
    (A : HilbertOperator (Qubits n)) :
    (zeroAncillaEmbeddedOperator a n A).conjTranspose =
      zeroAncillaEmbeddedOperator a n A.conjTranspose := by
  ext i j
  rcases (prodEquiv (m := a) (n := n)).surjective i with ⟨⟨x, y⟩, rfl⟩
  rcases (prodEquiv (m := a) (n := n)).surjective j with ⟨⟨x', y'⟩, rfl⟩
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;>
    simp [zeroAncillaEmbeddedOperator, Matrix.conjTranspose_apply, hx, hx']

/-- The zero-ancilla embedding of the identity is the all-zero ancilla
projector. -/
theorem zeroAncillaEmbeddedOperator_one {a n : Nat} :
    zeroAncillaEmbeddedOperator a n (1 : HilbertOperator (Qubits n)) =
      (OrthogonalProjector.zeroAncilla a n).op := by
  ext i j
  rcases (prodEquiv (m := a) (n := n)).surjective i with ⟨⟨x, y⟩, rfl⟩
  rcases (prodEquiv (m := a) (n := n)).surjective j with ⟨⟨x', y'⟩, rfl⟩
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;> by_cases hy : y = y' <;>
    simp [zeroAncillaEmbeddedOperator, OrthogonalProjector.zeroAncilla,
      OrthogonalProjector.tensor, OrthogonalProjector.zero, OrthogonalProjector.basis,
      OrthogonalProjector.basisOp, OrthogonalProjector.identity,
      HilbertOperator.tensor_apply, Matrix.one_apply, hx, hx', hy]

/-- The top-left block of the even branch of `P^{(SV)}` for a zero-ancilla
embedded operator is the even quotient applied to `A^*A`. -/
theorem projectedBlock_evenSingularValuePolynomial_zeroAncillaEmbeddedOperator {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    projectedBlock a n
        (evenSingularValuePolynomial (OrthogonalProjector.zeroAncilla a n) P
          (zeroAncillaEmbeddedOperator a n A)) =
      polynomialOperator (evenSquareQuotient P) (A.conjTranspose * A) := by
  unfold evenSingularValuePolynomial
  rw [← zeroAncillaEmbeddedOperator_one (a := a) (n := n)]
  rw [projectedBlock_mul_zeroAncillaEmbeddedOperator_right]
  rw [projectedBlock_zeroAncillaEmbeddedOperator_mul_left]
  rw [zeroAncillaEmbeddedOperator_conjTranspose, zeroAncillaEmbeddedOperator_mul]
  simp [projectedBlock_polynomialOperator_zeroAncillaEmbeddedOperator]

/-- The top-left block of the odd branch of `P^{(SV)}` for a zero-ancilla
embedded operator is the odd Hermitian functional-calculus branch on `A`. -/
theorem projectedBlock_oddSingularValuePolynomial_zeroAncillaEmbeddedOperator {a n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) :
    projectedBlock a n
        (oddSingularValuePolynomial P (zeroAncillaEmbeddedOperator a n A)) =
      A * polynomialOperator (oddSquareQuotient P) (A.conjTranspose * A) := by
  unfold oddSingularValuePolynomial
  rw [projectedBlock_zeroAncillaEmbeddedOperator_mul_left]
  rw [zeroAncillaEmbeddedOperator_conjTranspose, zeroAncillaEmbeddedOperator_mul]
  rw [projectedBlock_polynomialOperator_zeroAncillaEmbeddedOperator]

/-- Even Hermitian specialization of the singular-value polynomial:
`P^{(SV)}(A)=P(A)` when `A` is Hermitian and `P` has matching even parity. -/
theorem evenHermitianSingularValuePolynomial_eq_polynomialOperator {n L : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hL : L % 2 = 0) (hP : HasParity P L) :
    polynomialOperator (evenSquareQuotient P) (A.conjTranspose * A) =
      polynomialOperator P A := by
  have hpoly := evenSquareQuotient_comp_X_sq_of_hasParity hL hP
  rw [hA.eq]
  calc
    polynomialOperator (evenSquareQuotient P) (A * A) =
        Polynomial.aeval (A * A) (evenSquareQuotient P) := rfl
    _ = Polynomial.aeval A ((evenSquareQuotient P).comp (Polynomial.X ^ 2)) := by
      rw [Polynomial.aeval_comp]
      simp [pow_two]
    _ = Polynomial.aeval A P := by
      rw [hpoly]
    _ = polynomialOperator P A := rfl

/-- Odd Hermitian specialization of the singular-value polynomial:
`P^{(SV)}(A)=P(A)` when `A` is Hermitian and `P` has matching odd parity. -/
theorem oddHermitianSingularValuePolynomial_eq_polynomialOperator {n L : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hL : L % 2 = 1) (hP : HasParity P L) :
    A * polynomialOperator (oddSquareQuotient P) (A.conjTranspose * A) =
      polynomialOperator P A := by
  have hpoly := oddSquareQuotient_comp_X_sq_of_hasParity hL hP
  rw [hA.eq]
  calc
    A * polynomialOperator (oddSquareQuotient P) (A * A) =
        Polynomial.aeval A
          (Polynomial.X * (oddSquareQuotient P).comp (Polynomial.X ^ 2)) := by
      rw [map_mul, Polynomial.aeval_comp]
      simp [polynomialOperator, pow_two]
    _ = Polynomial.aeval A P := by
      rw [hpoly]
    _ = polynomialOperator P A := rfl

/-- Ordinary exact block encodings specialize projected QSVT's
`P^{(SV)}` target to the Hermitian polynomial target `P(A)`. -/
theorem projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
    {a n L : Nat} (P : Polynomial ℂ) (A : HilbertOperator (Qubits n))
    (hA : A.IsHermitian) (hP : HasParity P L) :
    projectedBlock a n
        (singularValuePolynomial (OrthogonalProjector.zeroAncilla a n) L P
          (zeroAncillaEmbeddedOperator a n A)) =
      polynomialOperator P A := by
  unfold singularValuePolynomial
  by_cases hL : L % 2 = 0
  · simp [hL, projectedBlock_evenSingularValuePolynomial_zeroAncillaEmbeddedOperator,
      evenHermitianSingularValuePolynomial_eq_polynomialOperator P A hA hL hP]
  · have hLodd : L % 2 = 1 := by omega
    simp [hL, projectedBlock_oddSingularValuePolynomial_zeroAncillaEmbeddedOperator,
      oddHermitianSingularValuePolynomial_eq_polynomialOperator P A hA hLodd hP]

theorem zeroAncilla_op_apply_prod (a n : Nat)
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    (OrthogonalProjector.zeroAncilla a n).op (prodEquiv (x, y)) (prodEquiv (x', y')) =
      (if x = 0 then if x' = 0 then if y = y' then (1 : ℂ) else 0 else 0 else 0) := by
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;> by_cases hy : y = y' <;>
    simp [OrthogonalProjector.zeroAncilla, OrthogonalProjector.tensor,
      OrthogonalProjector.zero, OrthogonalProjector.basis, OrthogonalProjector.basisOp,
      OrthogonalProjector.identity, HilbertOperator.tensor_apply, Matrix.one_apply, hx, hx', hy]

/-- Projecting a gate onto the all-zero ancilla block gives the full-space
operator that is zero outside the selected block and equal to the ordinary
projected block inside it. -/
theorem projected_zeroAncilla_entry {a n : Nat} (U : Gate (Qubits (a + n)))
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    projectedUnitaryBlock (OrthogonalProjector.zeroAncilla a n)
        (OrthogonalProjector.zeroAncilla a n) U
        (prodEquiv (x, y)) (prodEquiv (x', y')) =
      (if x = 0 then if x' = 0 then
        (U : HilbertOperator (Qubits (a + n))) (prodEquiv (0, y)) (prodEquiv (0, y'))
      else 0 else 0) := by
  unfold projectedUnitaryBlock
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (prodEquiv (0, y'))]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (prodEquiv (0, y))]
    · by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;>
        simp [zeroAncilla_op_apply_prod, hx, hx']
    · intro b hb
      rcases (prodEquiv (m := a) (n := n)).surjective b with ⟨⟨xb, yb⟩, rfl⟩
      simp only [zeroAncilla_op_apply_prod]
      by_cases hx : x = 0 <;> by_cases hxb : xb = 0 <;>
        by_cases hyb : y = yb <;> simp [hx, hxb, hyb] at hb ⊢
    · intro hb
      simp at hb
  · intro b hb
    rcases (prodEquiv (m := a) (n := n)).surjective b with ⟨⟨xb, yb⟩, rfl⟩
    simp only [zeroAncilla_op_apply_prod]
    by_cases hx' : x' = 0 <;> by_cases hxb : xb = 0 <;>
      by_cases hyb : yb = y' <;> simp [hx', hxb, hyb] at hb ⊢
  · intro hb
    simp at hb

/-- Ordinary exact block encodings are projected-unitary encodings with both
projectors selecting the all-zero ancilla block. -/
theorem exactBlockEncoding_to_projectedUnitaryEncoding {a n : Nat}
    {U : Gate (Qubits (a + n))} {A : HilbertOperator (Qubits n)}
    (h : ExactBlockEncoding a n U A) :
    ProjectedUnitaryEncoding (OrthogonalProjector.zeroAncilla a n)
      (OrthogonalProjector.zeroAncilla a n) U (zeroAncillaEmbeddedOperator a n A) := by
  constructor
  ext i j
  rcases (prodEquiv (m := a) (n := n)).surjective i with ⟨⟨x, y⟩, rfl⟩
  rcases (prodEquiv (m := a) (n := n)).surjective j with ⟨⟨x', y'⟩, rfl⟩
  rw [projected_zeroAncilla_entry]
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;>
    simp [zeroAncillaEmbeddedOperator, hx, hx', h.block_entry y y']

/-- Extract the `⟨+| V |+⟩` phase-ancilla block of a gate on one phase qubit
plus an `N`-qubit signal space.  This is the linear-algebraic core of the
`(\bra{+} \otimes -) V (\ket{+} \otimes -)` expression in
[GSLW19, BlockHam.tex:851-887]. -/
noncomputable def phasePlusBlock {N : Nat} (V : Gate (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  fun i j =>
    ∑ a : Fin (2 ^ 1), ∑ b : Fin (2 ^ 1),
      starRingEnd ℂ ((PureState.ketPlus : StateVector (Qubits 1)) a) *
        (V : HilbertOperator (Qubits (1 + N))) (prodEquiv (a, i)) (prodEquiv (b, j)) *
          ((PureState.ketPlus : StateVector (Qubits 1)) b)

/-- Conjugate a phase-ancilla circuit by a Hadamard on the phase qubit so that
the `|+⟩` block becomes an ordinary top-left `|0⟩` block. -/
noncomputable def phaseHadamardWrapper {N : Nat} (V : Gate (Qubits (1 + N))) :
    Gate (Qubits (1 + N)) :=
  Gate.tensor Gate.H (1 : Gate (Qubits N)) * V *
    Gate.tensor Gate.H (1 : Gate (Qubits N))

/-- Ancilla-indexed block of a gate acting on one phase qubit plus an `N`-qubit
signal space. -/
noncomputable def ancillaBlock {N : Nat} (a b : Fin (2 ^ 1))
    (V : Gate (Qubits (1 + N))) : HilbertOperator (Qubits N) :=
  fun i j => (V : HilbertOperator (Qubits (1 + N))) (prodEquiv (a, i)) (prodEquiv (b, j))

/-- Ancilla-indexed blocks multiply as ordinary block matrices. -/
theorem ancillaBlock_mul {N : Nat} (a c : Fin (2 ^ 1))
    (V W : Gate (Qubits (1 + N))) :
    ancillaBlock a c (V * W) =
      ∑ b : Fin (2 ^ 1), ancillaBlock a b V * ancillaBlock b c W := by
  ext i j
  change
    (∑ z : Fin (2 ^ (1 + N)),
      V.op (prodEquiv (a, i)) z * W.op z (prodEquiv (c, j))) =
    (∑ b : Fin (2 ^ 1), ∑ x : Fin (2 ^ N),
      V.op (prodEquiv (a, i)) (prodEquiv (b, x)) *
        W.op (prodEquiv (b, x)) (prodEquiv (c, j)))
  rw [← Equiv.sum_comp (prodEquiv (m := 1) (n := N))]
  simp [Fintype.sum_prod_type]

/-- Ancilla block of a tensor gate acting only on the phase qubit. -/
theorem ancillaBlock_tensor_left {N : Nat} (A : Gate (Qubits 1)) (a b : Fin (2 ^ 1)) :
    ancillaBlock a b (Gate.tensor A (1 : Gate (Qubits N))) =
      A a b • (1 : HilbertOperator (Qubits N)) := by
  ext i j
  by_cases hij : i = j <;>
    simp [ancillaBlock, Gate.tensor_apply, Matrix.smul_apply, hij]

/-- Rewrite the `⟨+|V|+⟩` block as a sum of ancilla-indexed matrix blocks.
This is the block-matrix form used by the phased-sequence proof [GSLW19,
BlockHam.tex:768-849]. -/
theorem phasePlusBlock_eq_sum_ancillaBlock {N : Nat}
    (V : Gate (Qubits (1 + N))) :
    phasePlusBlock V =
      ∑ a : Fin (2 ^ 1), ∑ b : Fin (2 ^ 1),
        starRingEnd ℂ ((PureState.ketPlus : StateVector (Qubits 1)) a) •
          (((PureState.ketPlus : StateVector (Qubits 1)) b) •
            ancillaBlock a b V) := by
  ext i j
  simp [phasePlusBlock, ancillaBlock, smul_eq_mul, mul_left_comm, mul_comm]

/-- The standard top-left block of the Hadamard-wrapped circuit is the same as
the `⟨+|V|+⟩` phase-ancilla block. -/
theorem projectedBlock_phaseHadamardWrapper {N : Nat} (V : Gate (Qubits (1 + N))) :
    projectedBlock 1 N
        (phaseHadamardWrapper V : HilbertOperator (Qubits (1 + N))) =
      phasePlusBlock V := by
  change ancillaBlock 0 0 (phaseHadamardWrapper V) = phasePlusBlock V
  rw [phasePlusBlock_eq_sum_ancillaBlock]
  unfold phaseHadamardWrapper
  rw [ancillaBlock_mul]
  simp only [ancillaBlock_mul, ancillaBlock_tensor_left, Nat.reducePow,
    Fin.isValue, Fin.sum_univ_two, Gate.H, Gate.HOp, Gate.coe_ofUnitary,
    PureState.ketPlus_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.smul_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, smul_smul, smul_eq_mul, mul_one]
  have hstar : (starRingEnd ℂ) PureState.invSqrt2 = PureState.invSqrt2 :=
    PureState.star_invSqrt2
  rw [hstar]
  simp only [smul_add, smul_smul]
  abel_nf

/-- Reassociate the phase ancilla plus an `m`-qubit block ancilla and an
`n`-qubit system from `1 + (m+n)` to `(1+m)+n`. -/
def phaseAncillaAssocEquiv (m n : Nat) :
    Fin (2 ^ (1 + (m + n))) ≃ Fin (2 ^ ((1 + m) + n)) :=
  finCongr (by rw [← Nat.add_assoc])

@[simp]
theorem phaseAncillaAssocEquiv_symm_zero {m n : Nat} (i : Fin (2 ^ n)) :
    (phaseAncillaAssocEquiv m n).symm
        (prodEquiv ((0 : Fin (2 ^ (1 + m))), i)) =
      prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), i)) := by
  apply Fin.ext
  simp [phaseAncillaAssocEquiv, prodEquiv, finProdFinEquiv, finCongr]

/-- Reindex a gate from the nested `1+(m+n)` layout to the standard
`(1+m)+n` block-encoding layout. -/
noncomputable def reassociatePhaseAncillaGate {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) : Gate (Qubits ((1 + m) + n)) :=
  Gate.ofUnitary
    (Matrix.reindex (phaseAncillaAssocEquiv m n) (phaseAncillaAssocEquiv m n)
      (V : HilbertOperator (Qubits (1 + (m + n)))))
    (reindex_mem_unitaryGroup (phaseAncillaAssocEquiv m n)
      (V : HilbertOperator (Qubits (1 + (m + n)))) V.unitary)

@[simp]
theorem reassociatePhaseAncillaGate_apply_zero {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) (i j : Fin (2 ^ n)) :
    (reassociatePhaseAncillaGate (m := m) (n := n) V :
        HilbertOperator (Qubits ((1 + m) + n)))
      (prodEquiv ((0 : Fin (2 ^ (1 + m))), i))
      (prodEquiv ((0 : Fin (2 ^ (1 + m))), j)) =
    (V : HilbertOperator (Qubits (1 + (m + n))))
      (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), i)))
      (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), j))) := by
  simp [reassociatePhaseAncillaGate, Matrix.reindex_apply]

/-- Taking the top-left block after Hadamard-wrapping and reassociating
ancillas is the same as first taking the phase `|+⟩` block and then the
ordinary `m`-ancilla block. -/
theorem projectedBlock_reassociatedPhaseHadamardWrapper {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) :
    projectedBlock (1 + m) n
        (reassociatePhaseAncillaGate (m := m) (n := n) (phaseHadamardWrapper V) :
          HilbertOperator (Qubits ((1 + m) + n))) =
      projectedBlock m n (phasePlusBlock V) := by
  ext i j
  have h :=
    congrFun
      (congrFun
        (projectedBlock_phaseHadamardWrapper V)
        (prodEquiv ((0 : Fin (2 ^ m)), i)))
      (prodEquiv ((0 : Fin (2 ^ m)), j))
  simpa [projectedBlock] using h

/-- Reassociating `1+(m+n)` to `(1+m)+n` exposes the same top-left block as
first taking the phase-ancilla `0,0` block and then the source-ancilla block. -/
theorem projectedBlock_reassociatePhaseAncillaGate {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) :
    projectedBlock (1 + m) n
        (reassociatePhaseAncillaGate (m := m) (n := n) V :
          HilbertOperator (Qubits ((1 + m) + n))) =
      projectedBlock m n (ancillaBlock 0 0 V) := by
  ext i j
  simp [projectedBlock, ancillaBlock]

/-- Projected `⟨+| V |+⟩` block with signal-space input/output projectors.
This matches `(\bra{+} \otimes Π_L) V (\ket{+} \otimes Π)` in the projected
QSVT public statement [GSLW19, BlockHam.tex:851-887]. -/
noncomputable def projectedPhasePlusBlock {N : Nat}
    (output input : OrthogonalProjector N) (V : Gate (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  output.op * phasePlusBlock V * input.op

/-- With both signal-space projectors selecting the all-zero source ancilla
block, the top-left system block of the projected phase block is just the
top-left system block of the underlying `⟨+|V|+⟩` phase block. -/
theorem projectedBlock_projectedPhasePlusBlock_zeroAncilla {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) :
    projectedBlock m n
        (projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
          (OrthogonalProjector.zeroAncilla m n) V) =
      projectedBlock m n (phasePlusBlock V) := by
  unfold projectedPhasePlusBlock
  rw [← zeroAncillaEmbeddedOperator_one (a := m) (n := n)]
  rw [projectedBlock_mul_zeroAncillaEmbeddedOperator_right]
  rw [projectedBlock_zeroAncillaEmbeddedOperator_mul_left]
  simp

end QSVT

namespace QSVT.Complement

/-- Namespace-local spelling of polynomial functional calculus on operators. -/
noncomputable abbrev polynomialOperator {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) : HilbertOperator (Qubits n) :=
  QuantumAlg.QSP.MultiQubit.QSVT.polynomialOperator P A

/-- Namespace-local spelling of a projected-unitary block. -/
abbrev projectedUnitaryBlock {N : Nat} (left right : OrthogonalProjector N)
    (U : Gate (Qubits N)) : HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.projectedUnitaryBlock left right U

/-- Namespace-local spelling of the parity-selected singular-value target. -/
noncomputable abbrev singularValuePolynomial {N : Nat}
    (input : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.singularValuePolynomial input L P A

/-- Namespace-local spelling of the projected phase-plus block. -/
noncomputable abbrev projectedPhasePlusBlock {N : Nat}
    (output input : OrthogonalProjector N) (V : Gate (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.projectedPhasePlusBlock output input V

/-- Namespace-local spelling of phase-ancilla reassociation for QSVT circuits. -/
noncomputable abbrev reassociatePhaseAncillaGate {m n : Nat}
    (V : Gate (Qubits (1 + (m + n)))) : Gate (Qubits ((1 + m) + n)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.reassociatePhaseAncillaGate V

end QSVT.Complement

end QSP.MultiQubit

end QuantumAlg
