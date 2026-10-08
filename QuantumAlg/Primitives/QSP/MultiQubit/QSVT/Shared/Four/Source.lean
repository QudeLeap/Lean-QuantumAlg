/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Branch
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Block

/-!
# Source polynomial certificates for the initialized native branches

Positive-degree bounds use the original matching-parity synthesis theorem.
The zero-degree bound uses the polynomial's known constant coefficient,
without querying or inspecting the source unitary.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private theorem exists_positive_branch {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) (degree : 0 < L) :
    ∃ phases : List ℝ, phases.length = L ∧
      projectedBlock m n (phasePlusBlock (initializedBranch U positive phases 1)) =
        polynomialOperator (realPolynomialToComplex P) A := by
  obtain ⟨phases, length, correct, _, _⟩ :=
    KnownZero.exists_real_word U positive true source degree
  have encoded := KnownZero.zeroBlockCircuit_correct U positive true phases encoding hermitian
    (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex source.parity) correct
  have block := encoded.projected_block_eq
  rw [KnownZero.zeroBlockCircuit_matrix, projectedBlock_reassociatedPhaseHadamardWrapper] at block
  exact ⟨phases, length, by simpa only [initializedBranch_one] using block⟩

/-- Every matching-parity source polynomial has a native branch, including the constant boundary. -/
theorem exists_initialized_polynomial_branch {m n L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ phases : List ℝ, ∃ constant : ℝ, phases.length = L ∧
      (0 < L → constant = 1) ∧
      projectedBlock m n (phasePlusBlock (initializedBranch U positive phases constant)) =
        polynomialOperator (realPolynomialToComplex P) A := by
  by_cases zero : L = 0
  · subst L
    have degree : P.natDegree = 0 := Nat.eq_zero_of_le_zero source.degree_le
    have constantPolynomial : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero degree
    have bound : |P.coeff 0| ≤ 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact source.bounded 0 (by constructor <;> norm_num)
    have polynomial : polynomialOperator (realPolynomialToComplex P) A =
        (P.coeff 0 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
      rw [constantPolynomial]
      simp [realPolynomialToComplex, polynomialOperator_C]
    refine ⟨[], P.coeff 0, rfl, by omega, ?_⟩
    rw [initializedBranch_constant_block U positive _ (abs_le.mp bound).1 (abs_le.mp bound).2]
    exact polynomial.symm
  · have degree : 0 < L := Nat.pos_of_ne_zero zero
    obtain ⟨phases, length, correct⟩ :=
      exists_positive_branch U positive A encoding hermitian source degree
    exact ⟨phases, 1, length, fun _ => rfl, correct⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
