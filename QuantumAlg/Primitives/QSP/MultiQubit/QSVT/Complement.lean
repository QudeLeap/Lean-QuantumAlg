/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Oracle.Reflection
public import QuantumAlg.Util.Polynomial.Basic
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Oracle.Reflection
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Util.Polynomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# QSVT spectral and projected-block support

Reusable polynomial, spectral, and projected-block support for projected QSVT.
-/

section

namespace QuantumAlg

namespace QSP.MultiQubit

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace QSVT


/-- Evaluate a complex polynomial on a finite-dimensional Hilbert operator via
Mathlib's algebraic polynomial evaluation. -/
public noncomputable def polynomialOperator {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) : HilbertOperator (Qubits n) :=
  Polynomial.aeval A P

/-- Polynomial evaluation on a diagonal matrix is pointwise evaluation on the
diagonal entries.  This is the finite-dimensional algebraic core used to connect
the QSVT polynomial statement with Mathlib's Hermitian spectral theorem. -/
lemma diagonal_aeval_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
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
lemma polynomialOperator_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
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

lemma left_tensor_one_apply_zero {a n : Nat} (V : UnitaryOperator (Qubits n))
    (i y : Fin (2 ^ n)) (x : Fin (2 ^ a)) :
    HilbertOperator.tensor (1 : HilbertOperator (Qubits a))
        (V : HilbertOperator (Qubits n))
      (prodEquiv (0, i)) (prodEquiv (x, y)) =
      (if x = 0 then V i y else 0) := by
  by_cases hx : x = 0
  · subst x
    simp [HilbertOperator.tensor_apply, Matrix.one_apply]
  · have h0x : ¬(0 : Fin (2 ^ a)) = x := fun h => hx h.symm
    simp [HilbertOperator.tensor_apply, hx, h0x]

lemma right_tensor_one_apply_zero {a n : Nat} (V : UnitaryOperator (Qubits n))
    (x : Fin (2 ^ a)) (y j : Fin (2 ^ n)) :
    HilbertOperator.tensor (1 : HilbertOperator (Qubits a))
        (V.dagger : HilbertOperator (Qubits n))
      (prodEquiv (x, y)) (prodEquiv (0, j)) =
      (if x = 0 then (V.dagger : HilbertOperator (Qubits n)) y j else 0) := by
  by_cases hx : x = 0 <;>
    simp [HilbertOperator.tensor_apply, Matrix.one_apply, hx]

lemma left_tensor_sum_collapse {a n : Nat} (V : UnitaryOperator (Qubits n))
    (D : UnitaryOperator (Qubits (a + n)))
    (i y : Fin (2 ^ n)) :
    (∑ z : Fin (2 ^ (a + n)),
      if (0 : Fin (2 ^ a)) = (prodEquiv.symm z).1 then
        V i (prodEquiv.symm z).2 * D z (prodEquiv (0, y))
      else 0) =
      ∑ x : Fin (2 ^ n), V i x * D (prodEquiv (0, x)) (prodEquiv (0, y)) := by
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [Fintype.sum_prod_type]

lemma projectedBlock_system_conjugate
    {a n : Nat} (V : UnitaryOperator (Qubits n))
    (D : UnitaryOperator (Qubits (a + n))) :
    projectedBlock a n
        (HilbertOperator.tensor (1 : HilbertOperator (Qubits a)) V *
          (D : HilbertOperator (Qubits (a + n))) *
          HilbertOperator.tensor (1 : HilbertOperator (Qubits a)) V.dagger) =
      (V : HilbertOperator (Qubits n)) *
        projectedBlock a n (D : HilbertOperator (Qubits (a + n))) *
        (V.dagger : HilbertOperator (Qubits n)) := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply,
    HilbertOperator.tensor_apply, Matrix.one_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [Fintype.sum_prod_type, left_tensor_sum_collapse]

/-- The metadata-free eigenbasis unitary of a Hermitian operator. -/
noncomputable def eigenbasisOperator {n : Nat} (A : HilbertOperator (Qubits n))
    (hA : A.IsHermitian) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix
    (hA.eigenvectorUnitary : HilbertOperator (Qubits n))
    hA.eigenvectorUnitary.property

/-- The eigenvalue-level polynomial data used by the Hermitian spectral
construction. -/
noncomputable def hermitianPolynomialEigenvalues {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) : Fin (2 ^ n) → ℂ :=
  fun i => P.eval ((hA.eigenvalues i : ℝ) : ℂ)

/-- A constructive unitary dilation of `P(A)` obtained by diagonalizing the
Hermitian operator, dilating each transformed eigenvalue, and conjugating back
to the computational basis. -/
noncomputable def hermitianPolynomialDilationOperator {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    UnitaryOperator (Qubits (1 + n)) := by
  let identity : UnitaryOperator (Qubits 1) := 1
  let basis := UnitaryOperator.tensor identity (eigenbasisOperator A hA)
  let dilation :=
    diagonalScalarDilationOperator (hermitianPolynomialEigenvalues P A hA) hcontract
  let basisDagger :=
    UnitaryOperator.tensor identity (eigenbasisOperator A hA).dagger
  exact basis * dilation * basisDagger

lemma hermitianPolynomialDilation_projectedBlock {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    projectedBlock 1 n
        (hermitianPolynomialDilationOperator P A hA hcontract :
          HilbertOperator (Qubits (1 + n))) =
      polynomialOperator P A := by
  unfold hermitianPolynomialDilationOperator
  change projectedBlock 1 n
      (HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          (eigenbasisOperator A hA : HilbertOperator (Qubits n)) *
        (diagonalScalarDilationOperator
          (hermitianPolynomialEigenvalues P A hA) hcontract :
            HilbertOperator (Qubits (1 + n))) *
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          ((eigenbasisOperator A hA).dagger : HilbertOperator (Qubits n))) =
      polynomialOperator P A
  rw [projectedBlock_system_conjugate,
    diagonalScalarDilationOperator_projectedBlock]
  rw [polynomialOperator, polynomialOperator_spectral P A hA]
  simp [eigenbasisOperator, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  congr 2

lemma hermitianPolynomialDilation_exactBlockEncoding {n : Nat} (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian)
    (hcontract : ∀ i, Complex.normSq (hermitianPolynomialEigenvalues P A hA i) <= 1) :
    ExactBlockEncoding 1 n (hermitianPolynomialDilationOperator P A hA hcontract)
      (polynomialOperator P A) := by
  constructor
  intro i j
  rw [hermitianPolynomialDilation_projectedBlock]

lemma hermitian_eigenvalue_norm_le_of_operator_norm_le_one {n : Nat}
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) (hnorm : ‖A‖ ≤ 1)
    (i : Fin (2 ^ n)) :
    ‖(hA.eigenvalues i : ℝ)‖ ≤ 1 := by
  have hspec : hA.eigenvalues i ∈ spectrum ℝ A :=
    hA.eigenvalues_mem_spectrum_real i
  exact (spectrum.norm_le_norm_of_mem hspec).trans hnorm

lemma hermitian_eigenvalue_mem_Icc_of_operator_norm_le_one {n : Nat}
    (A : HilbertOperator (Qubits n)) (hA : A.IsHermitian) (hnorm : ‖A‖ ≤ 1)
    (i : Fin (2 ^ n)) :
    hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnorm_i := hermitian_eigenvalue_norm_le_of_operator_norm_le_one A hA hnorm i
  simpa [Real.norm_eq_abs] using (abs_le.mp hnorm_i)

lemma hermitianPolynomialEigenvalues_contract_of_bound {n : Nat}
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
lemma polynomialOperator_X {n : Nat} (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.X : Polynomial ℂ) A = A := by
  simp [polynomialOperator]

@[simp]
lemma polynomialOperator_C {n : Nat} (c : ℂ) (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.C c : Polynomial ℂ) A =
      c • (1 : HilbertOperator (Qubits n)) := by
  ext i j
  by_cases h : i = j <;>
    simp [polynomialOperator, Matrix.algebraMap_matrix_apply, Matrix.smul_apply, h]

@[simp]
lemma polynomialOperator_C_mul {n : Nat} (c : ℂ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (Polynomial.C c * P) A = c • polynomialOperator P A := by
  ext i j
  simp [polynomialOperator, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
    Matrix.smul_apply]

/-- A constant polynomial acts as its scalar multiple of the identity under
functional calculus. -/
lemma polynomialOperator_eq_scalar_one_of_natDegree_eq_zero {n : Nat}
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (hdeg : P.natDegree = 0) :
    polynomialOperator P A = P.coeff 0 • (1 : HilbertOperator (Qubits n)) := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, polynomialOperator_C]
  simp

/-- Elementary eigenvector support lemma: powers of an operator preserve an
eigenvector with the corresponding powered eigenvalue. -/
lemma operatorPower_applyVec_of_eigenvector {N : Nat}
    (A : HilbertOperator (Qubits N)) («λ» : Complex)
    (v : HilbertVector (Qubits N))
    (hA : HilbertOperator.applyVec A v = «λ» • v) (k : Nat) :
    HilbertOperator.applyVec (A ^ k) v = «λ» ^ k • v := by
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
lemma polynomialOperator_applyVec_of_eigenvector {N : Nat}
    (P : Polynomial Complex) (A : HilbertOperator (Qubits N))
    («λ» : Complex) (v : HilbertVector (Qubits N))
    (hA : HilbertOperator.applyVec A v = «λ» • v) :
    HilbertOperator.applyVec (polynomialOperator P A) v = P.eval «λ» • v := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [polynomialOperator, map_add, HilbertOperator.add_applyVec, Polynomial.eval_add]
      rw [add_smul]
      rw [show ((Polynomial.aeval A) p).applyVec v = p.eval «λ» • v by
        simpa [polynomialOperator] using hp]
      rw [show ((Polynomial.aeval A) q).applyVec v = q.eval «λ» • v by
        simpa [polynomialOperator] using hq]
  | monomial k c =>
      have hscalar :
          ∀ w : HilbertVector (Qubits N),
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
        operatorPower_applyVec_of_eigenvector A «λ» v hA k,
        hscalar, smul_smul]

lemma polynomialOperator_add {n : Nat} (P Q : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (P + Q) A = polynomialOperator P A + polynomialOperator Q A := by
  simp [polynomialOperator]

lemma polynomialOperator_smul {n : Nat} (c : ℂ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits n)) :
    polynomialOperator (c • P) A = c • polynomialOperator P A := by
  rw [Polynomial.smul_eq_C_mul, polynomialOperator_C_mul]

/-- Polynomial functional calculus respects the real/imaginary and even/odd
coefficient split used in the arbitrary-parity QSVT reduction. This is an
elementary bookkeeping lemma supporting the four component construction in
[GSLW19, BlockHam.tex:1936-1952]. -/
lemma polynomialOperator_complex_fourPart_recompose {n : Nat}
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
lemma polynomialOperator_complex_fourPart_average_recompose {n : Nat}
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
lemma polynomialOperator_real_evenOdd_double_average_recompose {n : Nat}
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
lemma polynomialOperator_complex_evenOdd_double_average_recompose {n : Nat}
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
public def projectedUnitaryBlock {N : Nat} (left right : OrthogonalProjector N)
    (U : UnitaryOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  left.op * (U : HilbertOperator (Qubits N)) * right.op

/-- The projected block kills vectors in the input-projector complement.  This
is the input-side zero sector used in the source singular-invariant
decomposition [GSLW19, BlockHam.tex:599-611]. -/
lemma projectedUnitaryBlock_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : UnitaryOperator (Qubits N)}
    {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) ψ = ψ) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U) ψ = 0 := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hright_zero :
      HilbertOperator.applyVec right.op ψ = 0 :=
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      right hpsi
  rw [hright_zero]
  simp [HilbertOperator.applyVec]

/-- The projected block only sees the input's `right`-projector component. -/
lemma projectedUnitaryBlock_applyVec_projector_applyVec {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (ψ : HilbertVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
        (HilbertOperator.applyVec right.op ψ) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U) ψ := by
  unfold projectedUnitaryBlock
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hright :
      HilbertOperator.applyVec right.op (HilbertOperator.applyVec right.op ψ) =
        HilbertOperator.applyVec right.op ψ := by
    rw [← HilbertOperator.mul_applyVec, right.idempotent]
  rw [hright]

/-- The adjoint projected block only sees the output's `left`-projector
component. -/
lemma projectedUnitaryBlock_conjTranspose_applyVec_projector_applyVec {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (ψ : HilbertVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op ψ) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose ψ := by
  unfold projectedUnitaryBlock
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec,
    HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hleft :
      HilbertOperator.applyVec left.op (HilbertOperator.applyVec left.op ψ) =
        HilbertOperator.applyVec left.op ψ := by
    rw [← HilbertOperator.mul_applyVec, left.idempotent]
  rw [hleft]

/-- The projected-block Gram operator also kills vectors in the input-projector
complement [GSLW19, BlockHam.tex:599-611]. -/
lemma projectedUnitaryBlock_gram_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : UnitaryOperator (Qubits N)}
    {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) ψ = ψ) :
    HilbertOperator.applyVec
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U) ψ = 0 := by
  rw [HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_applyVec_eq_zero_of_right_complement (left := left)
      (right := right) (U := U) hpsi]
  simp [HilbertOperator.applyVec]

/-- Orthogonal projectors have L2 operator norm at most one.  This elementary
supporting fact is used to bound the singular values in the source
`def:singDec` decomposition [GSLW19, BlockHam.tex:570-613]. -/
lemma orthogonalProjector_norm_le_one {N : Nat} (P : OrthogonalProjector N) :
    ‖P.op‖ ≤ 1 := by
  have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self P.op
  rw [P.selfAdjoint, P.idempotent] at hnorm
  have hsq : ‖P.op‖ * ‖P.op‖ = ‖P.op‖ := hnorm.symm
  nlinarith [norm_nonneg P.op]

/-- Unitary operators have L2 operator norm one. -/
lemma gate_norm_eq_one {N : Nat} (U : UnitaryOperator (Qubits N)) :
    ‖(U : HilbertOperator (Qubits N))‖ = 1 :=
  CStarRing.norm_of_mem_unitary U.property

/-- Raw finite-register vector norm squared is the real part of its
star-dot-product.  This local bridge keeps the projected-singular-value proof
in matrix notation while using the Hilbert-space norm supplied by Mathlib. -/
lemma stateVector_norm_sq_eq_re_star_dot {N : Nat}
    (v : HilbertVector (Qubits N)) :
    ‖v‖ ^ 2 = RCLike.re ((star v.ofLp) ⬝ᵥ v.ofLp) := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [← Complex.ofReal_inj]
  simp [Complex.sq_norm, dotProduct, Complex.normSq_apply]

/-- Applying an operator has squared norm `v^* A^* A v`.  This is the Gram
identity used to pass from the spectral theorem for `A^*A` to source singular
values in `def:singDec` [GSLW19, BlockHam.tex:570-613]. -/
lemma applyVec_norm_sq_eq_re_star_dot_gram {N : Nat}
    (A : HilbertOperator (Qubits N)) (v : HilbertVector (Qubits N)) :
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
lemma inner_applyVec_applyVec {N : Nat}
    (A B : HilbertOperator (Qubits N))
    (ψ φ : HilbertVector (Qubits N)) :
    inner ℂ (HilbertOperator.applyVec A ψ) (HilbertOperator.applyVec B φ) =
      inner ℂ ψ (HilbertOperator.applyVec (A.conjTranspose * B) φ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, HilbertOperator.applyVec_apply]
  calc ∑ i, (∑ k, B i k * φ k) * starRingEnd ℂ (∑ j, A i j * ψ j)
      = ∑ i, ∑ k, ∑ j, (B i k * starRingEnd ℂ (A i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        ring
    _ = ∑ k, ∑ j, (∑ i, B i k * starRingEnd ℂ (A i j))
          * (φ k * starRingEnd ℂ (ψ j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, (A.conjTranspose * B) j k *
          (φ k * starRingEnd ℂ (ψ j)) := by
        refine Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun j _ => ?_
        congr 1
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Matrix.conjTranspose_apply,
            show star (A i j) = starRingEnd ℂ (A i j) from rfl, mul_comm]
    _ = ∑ j, (∑ k, (A.conjTranspose * B) j k * φ k) *
          starRingEnd ℂ (ψ j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring

/-- Applying a unitary operator after its adjoint returns the original vector. -/
lemma gate_applyVec_conjTranspose_applyVec {N : Nat}
    (U : UnitaryOperator (Qubits N)) (ψ : HilbertVector (Qubits N)) :
    U.applyVec (U.dagger.applyVec ψ) = ψ := by
  change HilbertOperator.applyVec (U : HilbertOperator (Qubits N))
    (HilbertOperator.applyVec (U.dagger : HilbertOperator (Qubits N)) ψ) = ψ
  rw [← HilbertOperator.mul_applyVec]
  have hUU :
      (U : HilbertOperator (Qubits N)) *
          (U.dagger : HilbertOperator (Qubits N)) =
        1 := by
    change (U : HilbertOperator (Qubits N)) *
          (U : HilbertOperator (Qubits N)).conjTranspose =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.property
  rw [hUU, HilbertOperator.one_applyVec]

/-- Applying a unitary operator's adjoint after the operator returns the original vector. -/
lemma gate_conjTranspose_applyVec_applyVec {N : Nat}
    (U : UnitaryOperator (Qubits N)) (ψ : HilbertVector (Qubits N)) :
    U.dagger.applyVec (U.applyVec ψ) = ψ := by
  change HilbertOperator.applyVec (U.dagger : HilbertOperator (Qubits N))
    (HilbertOperator.applyVec (U : HilbertOperator (Qubits N)) ψ) = ψ
  rw [← HilbertOperator.mul_applyVec]
  have hUU :
      (U.dagger : HilbertOperator (Qubits N)) *
          (U : HilbertOperator (Qubits N)) =
        1 := by
    change (U : HilbertOperator (Qubits N)).conjTranspose *
          (U : HilbertOperator (Qubits N)) =
        1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [hUU, HilbertOperator.one_applyVec]

/-- Applying a projector complement is subtracting the projector component. -/
lemma orthogonalProjector_complement_applyVec {N : Nat}
    (P : OrthogonalProjector N) (ψ : HilbertVector (Qubits N)) :
    HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ =
      ψ - HilbertOperator.applyVec P.op ψ := by
  unfold HilbertOperator.applyVec OrthogonalProjector.complement
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rfl

/-- A vector is the sum of its projector and complementary components. -/
lemma orthogonalProjector_applyVec_add_complement_applyVec {N : Nat}
    (P : OrthogonalProjector N) (ψ : HilbertVector (Qubits N)) :
    HilbertOperator.applyVec P.op ψ +
        HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ = ψ := by
  rw [orthogonalProjector_complement_applyVec]
  module

/-- A projector image is orthogonal to its complement. -/
lemma orthogonalProjector_inner_applyVec_complement {N : Nat}
    (P : OrthogonalProjector N) (ψ : HilbertVector (Qubits N)) :
    inner ℂ (HilbertOperator.applyVec P.op ψ)
      (HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ) = 0 := by
  rw [inner_applyVec_applyVec]
  rw [P.selfAdjoint, OrthogonalProjector.mul_complement]
  simp [HilbertOperator.applyVec]

/-- Orthogonal projectors split norm squares into image and complement parts. -/
lemma orthogonalProjector_norm_sq_decomposition {N : Nat}
    (P : OrthogonalProjector N) (ψ : HilbertVector (Qubits N)) :
    ‖ψ‖ ^ 2 =
      ‖HilbertOperator.applyVec P.op ψ‖ ^ 2 +
        ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ ^ 2 := by
  have hsum : P.op + OrthogonalProjector.complement P = (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  have hpsi :
      ψ =
        HilbertOperator.applyVec P.op ψ +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ := by
    calc
      ψ = HilbertOperator.applyVec (1 : HilbertOperator (Qubits N)) ψ := by
        rw [HilbertOperator.one_applyVec]
      _ = HilbertOperator.applyVec (P.op + OrthogonalProjector.complement P) ψ := by
        rw [hsum]
      _ = HilbertOperator.applyVec P.op ψ +
            HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ := by
        rw [HilbertOperator.add_applyVec]
  calc
    ‖ψ‖ ^ 2 =
        ‖HilbertOperator.applyVec P.op ψ +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ ^ 2 := by
      exact congrArg (fun x : HilbertVector (Qubits N) => ‖x‖ ^ 2) hpsi
    _ =
        ‖HilbertOperator.applyVec P.op ψ‖ ^ 2 +
          ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (HilbertOperator.applyVec P.op ψ)
          (HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ)
          (orthogonalProjector_inner_applyVec_complement P ψ)

/-- If an orthogonal projector preserves the norm of a unit vector, the vector
already lies in the projector image. -/
lemma orthogonalProjector_applyVec_eq_self_of_norm_eq_one {N : Nat}
    (P : OrthogonalProjector N) (ψ : NormalizedVector (Qubits N))
    (hproj : ‖HilbertOperator.applyVec P.op ψ‖ = 1) :
    HilbertOperator.applyVec P.op ψ = ψ := by
  have hdec := orthogonalProjector_norm_sq_decomposition P ψ
  rw [ψ.norm_eq_one, hproj] at hdec
  have hcomp_sq :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖]
  have hcomp_norm :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ = 0 := by
    nlinarith [norm_nonneg (HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ)]
  have hcomp_zero :
      HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ = 0 :=
    norm_eq_zero.mp hcomp_norm
  have hsum : P.op + OrthogonalProjector.complement P = (1 : HilbertOperator (Qubits N)) := by
    simp [OrthogonalProjector.complement]
  have hdecomp :
      ψ =
        HilbertOperator.applyVec P.op ψ +
          HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ := by
    calc
      ψ = HilbertOperator.applyVec (1 : HilbertOperator (Qubits N)) ψ := by
        rw [HilbertOperator.one_applyVec]
      _ = HilbertOperator.applyVec (P.op + OrthogonalProjector.complement P) ψ := by
        rw [hsum]
      _ = HilbertOperator.applyVec P.op ψ +
            HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ := by
        rw [HilbertOperator.add_applyVec]
  rw [hcomp_zero, add_zero] at hdecomp
  exact hdecomp.symm

/-- If a unit vector has projector component of norm `σ`, the complementary
projector component has norm `sqrt (1 - σ^2)`.  This is the normalization
identity used for the `0 < σ < 1` two-dimensional sectors in `lemma:singInvDec`
[GSLW19, BlockHam.tex:655-716]. -/
lemma orthogonalProjector_complement_norm_eq_sqrt {N : Nat}
    (P : OrthogonalProjector N) (ψ : NormalizedVector (Qubits N)) (σ : ℝ)
    (hproj : ‖HilbertOperator.applyVec P.op ψ‖ = σ) :
    ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ =
      Real.sqrt (1 - σ ^ 2) := by
  have hdec := orthogonalProjector_norm_sq_decomposition P ψ
  have hsq :
      ‖HilbertOperator.applyVec (OrthogonalProjector.complement P) ψ‖ ^ 2 =
        1 - σ ^ 2 := by
    rw [ψ.norm_eq_one, hproj] at hdec
    nlinarith
  have hnonneg : 0 ≤ 1 - σ ^ 2 := by
    rw [← hsq]
    exact sq_nonneg _
  rw [← Real.sq_sqrt hnonneg] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq

/-- Projected-unitary encodings are contractions.  This supplies the upper
singular-value bound used when splitting `def:singDec` into unit, nontrivial,
and kernel sectors [GSLW19, BlockHam.tex:570-613]. -/
lemma projectedUnitaryBlock_norm_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
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
lemma projectedUnitaryBlock_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    left.op * projectedUnitaryBlock left right U =
      projectedUnitaryBlock left right U := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      A * ((U : HilbertOperator (Qubits N)) * right.op))
    left.idempotent
  simpa [projectedUnitaryBlock, Matrix.mul_assoc] using h

/-- The projected block is supported on the right projector. -/
lemma projectedUnitaryBlock_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    projectedUnitaryBlock left right U * right.op =
      projectedUnitaryBlock left right U := by
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      (left.op * (U : HilbertOperator (Qubits N))) * A)
    right.idempotent
  simpa [projectedUnitaryBlock, Matrix.mul_assoc] using h

/-- The adjoint projected block is supported on the input projector from the
left. -/
lemma projectedUnitaryBlock_conjTranspose_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    right.op * (projectedUnitaryBlock left right U).conjTranspose =
      (projectedUnitaryBlock left right U).conjTranspose := by
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, left.selfAdjoint,
    right.selfAdjoint] using
      congrArg Matrix.conjTranspose
        (projectedUnitaryBlock_right_support left right U)

/-- The adjoint projected block is supported on the output projector from the
right. -/
lemma projectedUnitaryBlock_conjTranspose_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    (projectedUnitaryBlock left right U).conjTranspose * left.op =
      (projectedUnitaryBlock left right U).conjTranspose := by
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, left.selfAdjoint,
    right.selfAdjoint] using
      congrArg Matrix.conjTranspose
        (projectedUnitaryBlock_left_support left right U)

lemma projectedUnitaryBlock_conjTranspose_applyVec_left_supported {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec left.op ψ = ψ) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose ψ =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op ψ) := by
  rw [hpsi]

lemma projectedUnitaryBlock_conjTranspose_applyVec_left_support_reduce {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (ψ : HilbertVector (Qubits N)) :
    HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose
        (HilbertOperator.applyVec left.op ψ) =
      HilbertOperator.applyVec (projectedUnitaryBlock left right U).conjTranspose ψ := by
  rw [← HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_conjTranspose_right_support]

/-- The projected-block Gram operator is supported on the input projector from
the left.  This is the algebraic support fact used when converting the Gram
eigenbasis into the right singular-vector sector of `def:singDec` [GSLW19,
BlockHam.tex:570-613]. -/
lemma projectedUnitaryBlock_gram_left_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    right.op *
        ((projectedUnitaryBlock left right U).conjTranspose *
          projectedUnitaryBlock left right U) =
      (projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U := by
  rw [projectedUnitaryBlock]
  simp only [Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      (A * (Matrix.conjTranspose (U : HilbertOperator (Qubits N)) * left.op)) *
        (left.op * (U : HilbertOperator (Qubits N)) * right.op))
    right.idempotent
  simpa [Matrix.mul_assoc] using h

/-- The projected-block Gram operator is supported on the input projector from
the right. -/
lemma projectedUnitaryBlock_gram_right_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U) * right.op =
      (projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U := by
  rw [projectedUnitaryBlock]
  simp only [Matrix.conjTranspose_mul, left.selfAdjoint, right.selfAdjoint]
  have h := congrArg
    (fun A : HilbertOperator (Qubits N) =>
      (right.op * (Matrix.conjTranspose (U : HilbertOperator (Qubits N)) * left.op)) *
        (left.op * (U : HilbertOperator (Qubits N)) * A))
    right.idempotent
  simpa [Matrix.mul_assoc] using h

/-- The Gram operator `A† A` of a projected block is Hermitian.  This is the
Mathlib spectral-theorem entry point for constructing the singular-vector
decomposition used in `lemma:singInvDec` [GSLW19, BlockHam.tex:570-613]. -/
lemma projectedUnitaryBlock_gram_isHermitian {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self _

/-- The projected-block Gram operator is positive semidefinite, so its spectral
decomposition supplies nonnegative squared singular values [GSLW19,
BlockHam.tex:570-613]. -/
lemma projectedUnitaryBlock_gram_posSemidef {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    ((projectedUnitaryBlock left right U).conjTranspose *
      projectedUnitaryBlock left right U).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self _

/-- The projected-block Gram operator is a contraction. -/
lemma projectedUnitaryBlock_gram_norm_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
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
lemma projectedUnitaryBlock_gram_eigenvalues_nonneg {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    0 ≤ (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i :=
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg
    (projectedUnitaryBlock left right U) i

/-- Gram eigenvalues are at most one, because a projected-unitary block is a
contraction. -/
lemma projectedUnitaryBlock_gram_eigenvalues_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    OrthonormalBasis (Qubits N).Index ℂ (HilbertVector (Qubits N)) :=
  (projectedUnitaryBlock_gram_isHermitian left right U).eigenvectorBasis

/-- The output-side Gram operator `A A†` of a projected block.  This is the
adjoint-side spectral object needed for the left-kernel part of
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-611]. -/
def projectedUnitaryBlockLeftGram {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    HilbertOperator (Qubits N) :=
  projectedUnitaryBlock left right U * (projectedUnitaryBlock left right U).conjTranspose

/-- The output-side Gram operator `A A†` is Hermitian. -/
lemma projectedUnitaryBlockLeftGram_isHermitian {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    (projectedUnitaryBlockLeftGram left right U).IsHermitian := by
  simpa [projectedUnitaryBlockLeftGram] using
    Matrix.isHermitian_conjTranspose_mul_self
      ((projectedUnitaryBlock left right U).conjTranspose)

/-- Orthonormal eigenbasis of the output-side Gram operator. -/
noncomputable def projectedUnitaryBlockLeftGramEigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N)) :
    OrthonormalBasis (Qubits N).Index ℂ (HilbertVector (Qubits N)) :=
  (projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvectorBasis

/-- Output-side Gram eigenvector equation. -/
lemma projectedUnitaryBlockLeftGram_mulVec_eigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    Matrix.mulVec (projectedUnitaryBlockLeftGram left right U)
        ⇑(projectedUnitaryBlockLeftGramEigenbasis left right U i) =
      ((projectedUnitaryBlockLeftGram_isHermitian left right U).eigenvalues i : ℂ) •
        ⇑(projectedUnitaryBlockLeftGramEigenbasis left right U i) :=
  (projectedUnitaryBlockLeftGram_isHermitian left right U).mulVec_eigenvectorBasis i

/-- Norm-square bridge for applying `A†` to an output-side Gram eigenvector. -/
lemma projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_norm_sq
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
lemma projectedUnitaryBlock_conjTranspose_applyVec_leftGramEigenbasis_eq_zero_of_eigenvalue_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
lemma projectedUnitaryBlockGramEigenbasis_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    ‖(projectedUnitaryBlockGramEigenbasis left right U i :
      HilbertVector (Qubits N))‖ = 1 :=
  (projectedUnitaryBlockGramEigenbasis left right U).orthonormal.norm_eq_one i

/-- Eigenvector equation for the projected-block Gram eigenbasis. -/
lemma projectedUnitaryBlock_gram_mulVec_eigenbasis {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
lemma projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
  let «λ» : ℂ :=
    (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i
  have hev : Matrix.mulVec G v = «λ» • v := by
    dsimp [G, v, «λ»]
    exact projectedUnitaryBlock_gram_mulVec_eigenbasis left right U i
  have hsupport : right.op * G = G := by
    dsimp [G]
    exact projectedUnitaryBlock_gram_left_support left right U
  have hleft : Matrix.mulVec right.op (Matrix.mulVec G v) = Matrix.mulVec G v := by
    have hmat := congrArg (fun M : HilbertOperator (Qubits N) => Matrix.mulVec M v)
      hsupport
    simpa [Matrix.mulVec_mulVec] using hmat
  have hright :
      Matrix.mulVec right.op («λ» • v) = «λ» • Matrix.mulVec right.op v := by
    rw [Matrix.mulVec_smul]
  have h := congrArg (fun w => Matrix.mulVec right.op w) hev
  rw [hleft, hright] at h
  rw [hev] at h
  have hcancel := congrArg (fun w => «λ»⁻¹ • w) h.symm
  have hmul : «λ»⁻¹ * «λ» = 1 := inv_mul_cancel₀ hlambda
  simpa [smul_smul, hmul] using hcancel

/-- State-vector form of
`projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero`. -/
lemma projectedUnitaryBlockGramEigenbasis_right_applyVec_support_of_eigenvalue_ne_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec right.op
        (projectedUnitaryBlockGramEigenbasis left right U i : HilbertVector (Qubits N)) =
      (projectedUnitaryBlockGramEigenbasis left right U i : HilbertVector (Qubits N)) := by
  ext j
  simpa [HilbertOperator.applyVec_apply, Matrix.mulVec, dotProduct] using
    congrFun
      (projectedUnitaryBlockGramEigenbasis_right_support_of_eigenvalue_ne_zero
        left right U i hlambda) j

/-- Singular values induced by the projected-block Gram spectrum. -/
noncomputable def projectedUnitaryBlockSingularValue {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) : ℝ :=
  Real.sqrt ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i)

lemma projectedUnitaryBlockSingularValue_nonneg {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    0 ≤ projectedUnitaryBlockSingularValue left right U i :=
  Real.sqrt_nonneg _

lemma projectedUnitaryBlockSingularValue_sq {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    (projectedUnitaryBlockSingularValue left right U i) ^ 2 =
      (projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i := by
  rw [projectedUnitaryBlockSingularValue, Real.sq_sqrt]
  exact projectedUnitaryBlock_gram_eigenvalues_nonneg left right U i

/-- Singular values of a projected-unitary block lie in `[0,1]`, matching the
source sector parameter `σ` in `lemma:singInvDec` [GSLW19,
BlockHam.tex:570-613]. -/
lemma projectedUnitaryBlockSingularValue_le_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    projectedUnitaryBlockSingularValue left right U i ≤ 1 := by
  rw [projectedUnitaryBlockSingularValue, Real.sqrt_le_one]
  exact projectedUnitaryBlock_gram_eigenvalues_le_one left right U i

/-- A nonzero Gram eigenvalue gives a nonzero singular value. -/
lemma projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) : NormalizedVector (Qubits N) :=
  NormalizedVector.ofVector
    (projectedUnitaryBlockGramEigenbasis left right U i)
    (projectedUnitaryBlockGramEigenbasis_norm_eq_one left right U i)

/-- Right singular-vector candidates are normalized. -/
lemma projectedUnitaryBlockRightSingularVector_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    ‖(projectedUnitaryBlockRightSingularVector left right U i :
        HilbertVector (Qubits N))‖ = 1 :=
  (projectedUnitaryBlockRightSingularVector left right U i).norm_eq_one

/-- Left singular-vector candidate `σ⁻¹ A ψ` for nonzero singular-value
sectors.  The nonzero hypothesis is carried by the theorems using this
definition, keeping the definition total. -/
noncomputable def projectedUnitaryBlockLeftSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) : HilbertVector (Qubits N) :=
  ((projectedUnitaryBlockSingularValue left right U i : ℂ)⁻¹) •
    HilbertOperator.applyVec (projectedUnitaryBlock left right U)
      (projectedUnitaryBlockRightSingularVector left right U i)

lemma projectedUnitaryBlockRightSingularVector_support_of_eigenvalue_ne_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    HilbertOperator.applyVec right.op
        (projectedUnitaryBlockRightSingularVector left right U i) =
      projectedUnitaryBlockRightSingularVector left right U i := by
  simpa [projectedUnitaryBlockRightSingularVector] using
    projectedUnitaryBlockGramEigenbasis_right_applyVec_support_of_eigenvalue_ne_zero
      left right U i hlambda

lemma projectedUnitaryBlockLeftSingularVector_support {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index) :
    HilbertOperator.applyVec left.op
        (projectedUnitaryBlockLeftSingularVector left right U i) =
      projectedUnitaryBlockLeftSingularVector left right U i := by
  unfold projectedUnitaryBlockLeftSingularVector
  rw [HilbertOperator.applyVec_smul]
  congr 1
  rw [← HilbertOperator.mul_applyVec,
    projectedUnitaryBlock_left_support]

lemma projectedUnitaryBlock_applyVec_rightSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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

lemma projectedUnitaryBlock_gram_applyVec_rightSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
lemma projectedUnitaryBlock_applyVec_rightSingularVector_norm_sq {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
      (star ((projectedUnitaryBlockRightSingularVector left right U i :
          HilbertVector (Qubits N)).ofLp)) ⬝ᵥ
          ((projectedUnitaryBlockRightSingularVector left right U i :
            HilbertVector (Qubits N)).ofLp) = 1 := by
    have hnorm := projectedUnitaryBlockRightSingularVector_norm_eq_one left right U i
    have hinner :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ)
        (projectedUnitaryBlockRightSingularVector left right U i :
          HilbertVector (Qubits N))
    rw [EuclideanSpace.inner_eq_star_dotProduct, hnorm] at hinner
    norm_num at hinner
    simpa [dotProduct_comm] using hinner
  change RCLike.re
      ((star ((projectedUnitaryBlockRightSingularVector left right U i :
          HilbertVector (Qubits N)).ofLp)) ⬝ᵥ
        (((projectedUnitaryBlockSingularValue left right U i ^ 2 : ℝ) : ℂ) •
          ((projectedUnitaryBlockRightSingularVector left right U i :
            HilbertVector (Qubits N)).ofLp))) =
    projectedUnitaryBlockSingularValue left right U i ^ 2
  rw [dotProduct_smul, hdot, smul_eq_mul, mul_one]
  exact Complex.ofReal_re ((projectedUnitaryBlockSingularValue left right U i) ^ 2)

/-- A zero Gram eigenvalue gives a right-kernel vector for the projected block.
This is the entry point for the zero-singular-value part of
`lemma:singInvDec` [GSLW19, BlockHam.tex:599-611]. -/
lemma projectedUnitaryBlock_applyVec_rightSingularVector_eq_zero_of_eigenvalue_zero
    {N : Nat} (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
lemma projectedUnitaryBlockLeftSingularVector_norm_eq_one {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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

lemma projectedUnitaryBlock_conjTranspose_applyVec_leftSingularVector {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
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
  σ : ℝ
  sigma_pos : 0 < σ
  /-- Unit right singular vector supported by the input projector. -/
  rightVec : NormalizedVector (Qubits N)
  /-- Unit left singular vector supported by the output projector. -/
  leftVec : NormalizedVector (Qubits N)
  right_support :
    HilbertOperator.applyVec right.op rightVec = rightVec
  left_support :
    HilbertOperator.applyVec left.op leftVec = leftVec
  A_right :
    HilbertOperator.applyVec A rightVec = (σ : ℂ) • leftVec
  Astar_left :
    HilbertOperator.applyVec A.conjTranspose leftVec = (σ : ℂ) • rightVec

/-- Build the nonzero singular-vector pair attached to a nonzero Gram
eigenvalue.  The remaining `lemma:singInvDec` work is to split these pairs into
the `sigma=1` and `0<sigma<1` sectors and construct the source complement
vectors [GSLW19, BlockHam.tex:583-613,718-735]. -/
noncomputable def projectedUnitaryBlockNonzeroSingularPair {N : Nat}
    (left right : OrthogonalProjector N) (U : UnitaryOperator (Qubits N))
    (i : (Qubits N).Index)
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    SourceNonzeroSingularPair (projectedUnitaryBlock left right U) left right where
  σ := projectedUnitaryBlockSingularValue left right U i
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
  leftVec := NormalizedVector.ofVector
    (projectedUnitaryBlockLeftSingularVector left right U i)
    (projectedUnitaryBlockLeftSingularVector_norm_eq_one left right U i
      (projectedUnitaryBlockSingularValue_ne_zero_of_eigenvalue_ne_zero
        left right U i hlambda))
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
lemma sigma_mem_Ioc {N : Nat} {left right : OrthogonalProjector N}
    {U : UnitaryOperator (Qubits N)} {i : (Qubits N).Index}
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ ∈
      Set.Ioc (0 : ℝ) 1 := by
  constructor
  · exact (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).sigma_pos
  · exact projectedUnitaryBlockSingularValue_le_one left right U i

/-- The source singular-pair sector split: a nonzero singular value is either
the unit sector or the genuine two-dimensional sector. -/
lemma sigma_eq_one_or_lt_one {N : Nat} {left right : OrthogonalProjector N}
    {U : UnitaryOperator (Qubits N)} {i : (Qubits N).Index}
    (hlambda :
      ((projectedUnitaryBlock_gram_isHermitian left right U).eigenvalues i : ℂ) ≠ 0) :
    (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ = 1 ∨
      (projectedUnitaryBlockNonzeroSingularPair left right U i hlambda).σ < 1 := by
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
public noncomputable def singularValuePolynomial {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    HilbertOperator (Qubits N) :=
  if L % 2 = 0 then
    evenSingularValuePolynomial input P A
  else
    oddSingularValuePolynomial P A

/-- The even branch of `P^{(SV)}` kills the input-projector complement because
the target contains the input projector on the right. -/
lemma evenSingularValuePolynomial_applyVec_eq_zero_of_input_complement {N : Nat}
    {input : OrthogonalProjector N} {A : HilbertOperator (Qubits N)}
    (P : Polynomial ℂ) {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement input) ψ = ψ) :
    HilbertOperator.applyVec (evenSingularValuePolynomial input P A) ψ = 0 := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec]
  have hinput_zero :
      HilbertOperator.applyVec input.op ψ = 0 :=
    OrthogonalProjector.projector_applyVec_eq_zero_of_complement_applyVec_eq_self
      input hpsi
  rw [hinput_zero]
  simp [HilbertOperator.applyVec]

/-- The odd branch of `P^{(SV)}` kills the input-projector complement for a
projected unitary block: the Gram operator has eigenvalue `0` there, and the
leading projected block kills the remaining scalar multiple. -/
lemma oddSingularValuePolynomial_applyVec_eq_zero_of_right_complement {N : Nat}
    {left right : OrthogonalProjector N} {U : UnitaryOperator (Qubits N)}
    (P : Polynomial ℂ) {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) ψ = ψ) :
    HilbertOperator.applyVec
        (oddSingularValuePolynomial P (projectedUnitaryBlock left right U)) ψ = 0 := by
  have hgram :
      HilbertOperator.applyVec
          ((projectedUnitaryBlock left right U).conjTranspose *
            projectedUnitaryBlock left right U) ψ =
        (0 : ℂ) • ψ := by
    rw [zero_smul]
    exact projectedUnitaryBlock_gram_applyVec_eq_zero_of_right_complement
      (left := left) (right := right) (U := U) hpsi
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      ((projectedUnitaryBlock left right U).conjTranspose *
        projectedUnitaryBlock left right U) 0 ψ hgram,
    HilbertOperator.applyVec_smul,
    projectedUnitaryBlock_applyVec_eq_zero_of_right_complement (left := left)
      (right := right) (U := U) hpsi]
  simp

/-- The parity-selected singular-value polynomial target kills vectors in the
input-projector complement for projected-unitary encodings. -/
lemma singularValuePolynomial_applyVec_eq_zero_of_right_complement {N L : Nat}
    {left right : OrthogonalProjector N} {U : UnitaryOperator (Qubits N)}
    (P : Polynomial ℂ) {ψ : HilbertVector (Qubits N)}
    (hpsi : HilbertOperator.applyVec (OrthogonalProjector.complement right) ψ = ψ) :
    HilbertOperator.applyVec
        (singularValuePolynomial right L P (projectedUnitaryBlock left right U)) ψ = 0 := by
  unfold singularValuePolynomial
  by_cases hL : L % 2 = 0
  · simp [hL, evenSingularValuePolynomial_applyVec_eq_zero_of_input_complement
      P hpsi]
  · simp [hL, oddSingularValuePolynomial_applyVec_eq_zero_of_right_complement
      (left := left) (right := right) (U := U) P hpsi]

@[simp]
lemma singularValuePolynomial_X_one {N : Nat} (input : OrthogonalProjector N)
    (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input 1 (Polynomial.X : Polynomial ℂ) A = A := by
  unfold singularValuePolynomial oddSingularValuePolynomial polynomialOperator
  simp

lemma evenSingularValuePolynomial_add {N : Nat} (input : OrthogonalProjector N)
    (P Q : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    evenSingularValuePolynomial input (P + Q) A =
      evenSingularValuePolynomial input P A + evenSingularValuePolynomial input Q A := by
  unfold evenSingularValuePolynomial
  rw [evenSquareQuotient_add, polynomialOperator_add]
  simp [Matrix.mul_add, Matrix.add_mul]

lemma evenSingularValuePolynomial_smul {N : Nat} (input : OrthogonalProjector N)
    (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    evenSingularValuePolynomial input (c • P) A =
      c • evenSingularValuePolynomial input P A := by
  unfold evenSingularValuePolynomial
  rw [evenSquareQuotient_smul, polynomialOperator_smul]
  simp

lemma oddSingularValuePolynomial_add {N : Nat} (P Q : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) :
    oddSingularValuePolynomial (P + Q) A =
      oddSingularValuePolynomial P A + oddSingularValuePolynomial Q A := by
  unfold oddSingularValuePolynomial
  rw [oddSquareQuotient_add, polynomialOperator_add]
  simp [Matrix.mul_add]

lemma oddSingularValuePolynomial_smul {N : Nat}
    (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    oddSingularValuePolynomial (c • P) A =
      c • oddSingularValuePolynomial P A := by
  unfold oddSingularValuePolynomial
  rw [oddSquareQuotient_smul, polynomialOperator_smul]
  simp

lemma singularValuePolynomial_add {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (P Q : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input L (P + Q) A =
      singularValuePolynomial input L P A + singularValuePolynomial input L Q A := by
  unfold singularValuePolynomial
  by_cases h : L % 2 = 0
  · simp [h, evenSingularValuePolynomial_add]
  · simp [h, oddSingularValuePolynomial_add]

lemma singularValuePolynomial_smul {N : Nat} (input : OrthogonalProjector N)
    (L : ℕ) (c : ℂ) (P : Polynomial ℂ) (A : HilbertOperator (Qubits N)) :
    singularValuePolynomial input L (c • P) A =
      c • singularValuePolynomial input L P A := by
  unfold singularValuePolynomial
  by_cases h : L % 2 = 0
  · simp [h, evenSingularValuePolynomial_smul]
  · simp [h, oddSingularValuePolynomial_smul]

/-- Polynomial average identities lift through the singular-value polynomial
operation used in `cor:matchingParity` [GSLW19, BlockHam.tex:851-887]. -/
lemma singularValuePolynomial_average_of_polynomial_average {N : Nat}
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
lemma singularPair_gram_applyVec_rightVec {N : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right) :
    HilbertOperator.applyVec (A.conjTranspose * A) pair.rightVec =
      ((pair.σ : Complex) ^ 2) • pair.rightVec := by
  rw [HilbertOperator.mul_applyVec, pair.A_right, HilbertOperator.applyVec_smul,
    pair.Astar_left, smul_smul]
  ring_nf

/-- Even branch of `P^{(SV)}` on a right singular vector: the quotient
polynomial evaluates at `sigma^2`, hence the full target scalar is `P(sigma)`
[GSLW19, BlockHam.tex:747-764]. -/
lemma evenSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec (evenSingularValuePolynomial right P A) pair.rightVec =
      P.eval (pair.σ : Complex) • pair.rightVec := by
  unfold evenSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec, HilbertOperator.mul_applyVec, pair.right_support,
    polynomialOperator_applyVec_of_eigenvector (evenSquareQuotient P)
      (A.conjTranspose * A) ((pair.σ : Complex) ^ 2) pair.rightVec
      (singularPair_gram_applyVec_rightVec pair),
    evenSquareQuotient_eval_sq_of_hasParity hL hP,
    HilbertOperator.applyVec_smul, pair.right_support]

/-- Odd branch of `P^{(SV)}` on a right singular vector: after applying the
quotient polynomial to `A^*A`, the leading `A` maps to the left singular vector
and contributes the missing factor `sigma` [GSLW19, BlockHam.tex:747-764]. -/
lemma oddSingularValuePolynomial_applyVec_rightVec {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec (oddSingularValuePolynomial P A) pair.rightVec =
      P.eval (pair.σ : Complex) • pair.leftVec := by
  unfold oddSingularValuePolynomial
  rw [HilbertOperator.mul_applyVec,
    polynomialOperator_applyVec_of_eigenvector (oddSquareQuotient P)
      (A.conjTranspose * A) ((pair.σ : Complex) ^ 2) pair.rightVec
      (singularPair_gram_applyVec_rightVec pair),
    HilbertOperator.applyVec_smul, pair.A_right, smul_smul]
  have hodd := oddSquareQuotient_eval_sq_of_hasParity hL hP (pair.σ : Complex)
  rw [← hodd]
  ring_nf

/-- Even-parity branch of the parity-selected singular-value target on a
right singular vector [GSLW19, BlockHam.tex:747-764]. -/
lemma singularValuePolynomial_applyVec_rightVec_of_even {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 0) (hP : HasParity P L) :
    HilbertOperator.applyVec (singularValuePolynomial right L P A) pair.rightVec =
      P.eval (pair.σ : Complex) • pair.rightVec := by
  unfold singularValuePolynomial
  simp [hL, evenSingularValuePolynomial_applyVec_rightVec pair P hL hP]

/-- Odd-parity branch of the parity-selected singular-value target on a right
singular vector [GSLW19, BlockHam.tex:747-764]. -/
lemma singularValuePolynomial_applyVec_rightVec_of_odd {N L : Nat}
    {A : HilbertOperator (Qubits N)} {left right : OrthogonalProjector N}
    (pair : SourceNonzeroSingularPair A left right)
    (P : Polynomial Complex) (hL : L % 2 = 1) (hP : HasParity P L) :
    HilbertOperator.applyVec (singularValuePolynomial right L P A) pair.rightVec =
      P.eval (pair.σ : Complex) • pair.leftVec := by
  unfold singularValuePolynomial
  have hnot : ¬ L % 2 = 0 := by omega
  simp [hnot, oddSingularValuePolynomial_applyVec_rightVec pair P hL hP]

/-- A projected-unitary encoding of a full-space operator by a unitary operator and
two orthogonal projectors.  Ordinary block encodings are the special case where
both projectors select the all-zero ancilla block. -/
structure ProjectedUnitaryEncoding {N : Nat} (left right : OrthogonalProjector N)
    (U : UnitaryOperator (Qubits N)) (A : HilbertOperator (Qubits N)) : Prop where
  block_eq : projectedUnitaryBlock left right U = A

lemma ProjectedUnitaryEncoding.block_entry {N : Nat}
    {left right : OrthogonalProjector N} {U : UnitaryOperator (Qubits N)}
    {A : HilbertOperator (Qubits N)}
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
lemma projectedBlock_zeroAncillaEmbeddedOperator {a n : Nat}
    (A : HilbertOperator (Qubits n)) :
    projectedBlock a n (zeroAncillaEmbeddedOperator a n A) = A := by
  ext i j
  simp [projectedBlock, zeroAncillaEmbeddedOperator]

/-- Multiplication is preserved inside the zero-ancilla embedded block. -/
lemma zeroAncillaEmbeddedOperator_mul {a n : Nat}
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
lemma zeroAncillaEmbeddedOperator_pow_succ {a n : Nat}
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
lemma projectedBlock_zeroAncillaEmbeddedOperator_pow {a n : Nat}
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
lemma projectedBlock_zeroAncillaEmbeddedOperator_mul_left {a n : Nat}
    (A : HilbertOperator (Qubits n)) (M : HilbertOperator (Qubits (a + n))) :
    projectedBlock a n (zeroAncillaEmbeddedOperator a n A * M) =
      A * projectedBlock a n M := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [zeroAncillaEmbeddedOperator, Fintype.sum_prod_type]

/-- The top-left block of `M * zeroAncillaEmbeddedOperator A` is the top-left
block of `M` times `A`. -/
lemma projectedBlock_mul_zeroAncillaEmbeddedOperator_right {a n : Nat}
    (M : HilbertOperator (Qubits (a + n))) (A : HilbertOperator (Qubits n)) :
    projectedBlock a n (M * zeroAncillaEmbeddedOperator a n A) =
      projectedBlock a n M * A := by
  ext i j
  simp only [projectedBlock, Matrix.mul_apply]
  rw [← Equiv.sum_comp (prodEquiv (m := a) (n := n))]
  simp [zeroAncillaEmbeddedOperator, Fintype.sum_prod_type]

/-- The top-left block of a polynomial in a zero-ancilla embedded operator is
the corresponding polynomial in the system operator. -/
lemma projectedBlock_polynomialOperator_zeroAncillaEmbeddedOperator {a n : Nat}
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
lemma zeroAncillaEmbeddedOperator_conjTranspose {a n : Nat}
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
lemma zeroAncillaEmbeddedOperator_one {a n : Nat} :
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
lemma projectedBlock_evenSingularValuePolynomial_zeroAncillaEmbeddedOperator {a n : Nat}
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
lemma projectedBlock_oddSingularValuePolynomial_zeroAncillaEmbeddedOperator {a n : Nat}
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
lemma evenHermitianSingularValuePolynomial_eq_polynomialOperator {n L : Nat}
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
lemma oddHermitianSingularValuePolynomial_eq_polynomialOperator {n L : Nat}
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
lemma projectedBlock_singularValuePolynomial_zeroAncillaEmbeddedOperator_of_hermitian
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

lemma zeroAncilla_op_apply_prod (a n : Nat)
    (x x' : Fin (2 ^ a)) (y y' : Fin (2 ^ n)) :
    (OrthogonalProjector.zeroAncilla a n).op (prodEquiv (x, y)) (prodEquiv (x', y')) =
      (if x = 0 then if x' = 0 then if y = y' then (1 : ℂ) else 0 else 0 else 0) := by
  by_cases hx : x = 0 <;> by_cases hx' : x' = 0 <;> by_cases hy : y = y' <;>
    simp [OrthogonalProjector.zeroAncilla, OrthogonalProjector.tensor,
      OrthogonalProjector.zero, OrthogonalProjector.basis, OrthogonalProjector.basisOp,
      OrthogonalProjector.identity, HilbertOperator.tensor_apply, Matrix.one_apply, hx, hx', hy]

/-- Projecting a unitary onto the all-zero ancilla block gives the full-space
operator that is zero outside the selected block and equal to the ordinary
projected block inside it. -/
lemma projected_zeroAncilla_entry {a n : Nat}
    (U : UnitaryOperator (Qubits (a + n)))
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
lemma exactBlockEncoding_to_projectedUnitaryEncoding {a n : Nat}
    {U : UnitaryOperator (Qubits (a + n))} {A : HilbertOperator (Qubits n)}
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

/-- Extract the `⟨+| V |+⟩` phase-ancilla block of a unitary on one phase qubit
plus an `N`-qubit signal space.  This is the linear-algebraic core of the
`(\bra{+} \otimes -) V (\ket{+} \otimes -)` expression in
[GSLW19, BlockHam.tex:851-887]. -/
noncomputable def phasePlusBlock {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  fun i j =>
    ∑ a : Fin (2 ^ 1), ∑ b : Fin (2 ^ 1),
      starRingEnd ℂ ((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) a) *
        (V : HilbertOperator (Qubits (1 + N))) (prodEquiv (a, i)) (prodEquiv (b, j)) *
          ((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) b)

/-- Metadata-free Hadamard conjugation on the phase ancilla. -/
noncomputable def phaseHadamardWrapperOperator {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) : UnitaryOperator (Qubits (1 + N)) := by
  let identity : UnitaryOperator (Qubits N) := 1
  let hadamard := UnitaryOperator.tensor Gate.HOp identity
  exact hadamard * V * hadamard

/-- Ancilla-indexed block of an operator acting on one phase qubit plus an `N`-qubit
signal space. -/
noncomputable def ancillaBlock {N : Nat} (a b : Fin (2 ^ 1))
    (V : HilbertOperator (Qubits (1 + N))) : HilbertOperator (Qubits N) :=
  fun i j => V (prodEquiv (a, i)) (prodEquiv (b, j))

/-- Ancilla-indexed blocks multiply as ordinary block matrices. -/
lemma ancillaBlock_mul {N : Nat} (a c : Fin (2 ^ 1))
    (V W : HilbertOperator (Qubits (1 + N))) :
    ancillaBlock a c (V * W) =
      ∑ b : Fin (2 ^ 1), ancillaBlock a b V * ancillaBlock b c W := by
  ext i j
  change
    (∑ z : Fin (2 ^ (1 + N)),
      V (prodEquiv (a, i)) z * W z (prodEquiv (c, j))) =
    (∑ b : Fin (2 ^ 1), ∑ x : Fin (2 ^ N),
      V (prodEquiv (a, i)) (prodEquiv (b, x)) *
        W (prodEquiv (b, x)) (prodEquiv (c, j)))
  rw [← Equiv.sum_comp (prodEquiv (m := 1) (n := N))]
  simp [Fintype.sum_prod_type]

/-- Ancilla block of a tensor unitary acting only on the phase qubit. -/
lemma ancillaBlock_tensor_left {N : Nat} (A : UnitaryOperator (Qubits 1))
    (a b : Fin (2 ^ 1)) :
    ancillaBlock a b
        (HilbertOperator.tensor (A : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits N))) =
      A a b • (1 : HilbertOperator (Qubits N)) := by
  ext i j
  simp only [ancillaBlock, HilbertOperator.tensor_apply]
  have hai := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := N)) (a, i)
  have hbj := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := N)) (b, j)
  rw [hai, hbj]
  change A a b * (1 : HilbertOperator (Qubits N)) i j =
    (A a b • (1 : HilbertOperator (Qubits N))) i j
  by_cases hij : i = j <;>
    simp [Matrix.one_apply, Matrix.smul_apply, hij]

/-- Rewrite the `⟨+|V|+⟩` block as a sum of ancilla-indexed matrix blocks.
This is the block-matrix form used by the phased-sequence proof [GSLW19,
BlockHam.tex:768-849]. -/
lemma phasePlusBlock_eq_sum_ancillaBlock {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) :
    phasePlusBlock V =
      ∑ a : Fin (2 ^ 1), ∑ b : Fin (2 ^ 1),
        starRingEnd ℂ ((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) a) •
          (((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) b) •
            ancillaBlock a b (V : HilbertOperator (Qubits (1 + N)))) := by
  ext i j
  simp [phasePlusBlock, ancillaBlock, smul_eq_mul, mul_left_comm, mul_comm]

/-- The standard top-left block of the Hadamard-wrapped circuit is the same as
the `⟨+|V|+⟩` phase-ancilla block. -/
lemma projectedBlock_phaseHadamardWrapper {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) :
    projectedBlock 1 N
        (phaseHadamardWrapperOperator V : HilbertOperator (Qubits (1 + N))) =
      phasePlusBlock V := by
  change ancillaBlock 0 0 (phaseHadamardWrapperOperator V) = phasePlusBlock V
  rw [phasePlusBlock_eq_sum_ancillaBlock]
  change ancillaBlock 0 0
      (HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits N)) *
        (V : HilbertOperator (Qubits (1 + N))) *
        HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits N))) =
    ∑ a : Fin (2 ^ 1), ∑ b : Fin (2 ^ 1),
      starRingEnd ℂ ((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) a) •
        (((NormalizedVector.ketPlus : HilbertVector (Qubits 1)) b) •
          ancillaBlock a b (V : HilbertOperator (Qubits (1 + N))))
  have hH00 :
      (Gate.HOp : HilbertOperator (Qubits 1)) 0 0 = NormalizedVector.invSqrt2 := by
    simp [Gate.HOp]
  have hH01 :
      (Gate.HOp : HilbertOperator (Qubits 1)) 0 1 = NormalizedVector.invSqrt2 := by
    simp [Gate.HOp]
  have hH10 :
      (Gate.HOp : HilbertOperator (Qubits 1)) 1 0 = NormalizedVector.invSqrt2 := by
    simp [Gate.HOp]
  have hleft (c : Fin (2 ^ 1)) :
      ancillaBlock 0 c
          (HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1))
              (1 : HilbertOperator (Qubits N)) *
            (V : HilbertOperator (Qubits (1 + N)))) =
        NormalizedVector.invSqrt2 • ancillaBlock 0 c V +
          NormalizedVector.invSqrt2 • ancillaBlock 1 c V := by
    rw [ancillaBlock_mul]
    simp only [Nat.reducePow, Fin.sum_univ_two, ancillaBlock_tensor_left,
      hH00, hH01, Matrix.smul_mul, Matrix.one_mul]
  rw [ancillaBlock_mul]
  simp_rw [hleft]
  simp only [ancillaBlock_tensor_left, Nat.reducePow, Fin.isValue,
    Fin.sum_univ_two, hH00, hH10, NormalizedVector.ketPlus_apply,
    Matrix.mul_smul, smul_smul, mul_one]
  have hstar : (starRingEnd ℂ) NormalizedVector.invSqrt2 = NormalizedVector.invSqrt2 :=
    NormalizedVector.star_invSqrt2
  rw [hstar]
  simp only [smul_add, smul_smul]
  abel_nf

@[simp]
lemma phaseAncillaAssocEquiv_symm_zero {m n : Nat} (i : Fin (2 ^ n)) :
    (phaseAncillaAssocEquiv m n).symm
        (prodEquiv ((0 : Fin (2 ^ (1 + m))), i)) =
      prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), i)) := by
  apply Fin.ext
  simp [phaseAncillaAssocEquiv, prodEquiv, finProdFinEquiv, finCongr]

@[simp]
lemma reassociatePhaseAncillaOperator_apply_zero {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) (i j : Fin (2 ^ n)) :
    (reassociatePhaseAncillaOperator (m := m) (n := n) V :
        HilbertOperator (Qubits ((1 + m) + n)))
      (prodEquiv ((0 : Fin (2 ^ (1 + m))), i))
      (prodEquiv ((0 : Fin (2 ^ (1 + m))), j)) =
    (V : HilbertOperator (Qubits (1 + (m + n))))
      (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), i)))
      (prodEquiv ((0 : Fin (2 ^ 1)), prodEquiv ((0 : Fin (2 ^ m)), j))) := by
  simp [reassociatePhaseAncillaOperator, Matrix.reindex_apply]

/-- Taking the top-left block after Hadamard-wrapping and reassociating
ancillas is the same as first taking the phase `|+⟩` block and then the
ordinary `m`-ancilla block. -/
lemma projectedBlock_reassociatedPhaseHadamardWrapper {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) :
    projectedBlock (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n)
            (phaseHadamardWrapperOperator V) :
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
lemma projectedBlock_reassociatePhaseAncillaOperator {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) :
    projectedBlock (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n) V :
          HilbertOperator (Qubits ((1 + m) + n))) =
      projectedBlock m n
        (ancillaBlock 0 0 (V : HilbertOperator (Qubits (1 + (m + n))))) := by
  ext i j
  simp [projectedBlock, ancillaBlock]

/-- Projected `⟨+| V |+⟩` block with signal-space input/output projectors.
This matches `(\bra{+} \otimes Π_L) V (\ket{+} \otimes Π)` in the projected
QSVT public statement [GSLW19, BlockHam.tex:851-887]. -/
public noncomputable def projectedPhasePlusBlock {N : Nat}
    (output input : OrthogonalProjector N)
    (V : UnitaryOperator (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  output.op * phasePlusBlock V * input.op

/-- With both signal-space projectors selecting the all-zero source ancilla
block, the top-left system block of the projected phase block is just the
top-left system block of the underlying `⟨+|V|+⟩` phase block. -/
lemma projectedBlock_projectedPhasePlusBlock_zeroAncilla {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) :
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
    (U : UnitaryOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.projectedUnitaryBlock left right U

/-- Namespace-local spelling of the parity-selected singular-value target. -/
noncomputable abbrev singularValuePolynomial {N : Nat}
    (input : OrthogonalProjector N) (L : ℕ) (P : Polynomial ℂ)
    (A : HilbertOperator (Qubits N)) : HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.singularValuePolynomial input L P A

/-- Namespace-local spelling of the projected phase-plus block. -/
noncomputable abbrev projectedPhasePlusBlock {N : Nat}
    (output input : OrthogonalProjector N)
    (V : UnitaryOperator (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  QuantumAlg.QSP.MultiQubit.QSVT.projectedPhasePlusBlock output input V

/-- Namespace-local spelling of metadata-free phase-ancilla reassociation. -/
noncomputable abbrev reassociatePhaseAncillaOperator {m n : Nat}
    (V : UnitaryOperator (Qubits (1 + (m + n)))) :
    UnitaryOperator (Qubits ((1 + m) + n)) :=
  QuantumAlg.QSP.MultiQubit.QSVT.reassociatePhaseAncillaOperator V

end QSVT.Complement

end QSP.MultiQubit

end QuantumAlg

end
