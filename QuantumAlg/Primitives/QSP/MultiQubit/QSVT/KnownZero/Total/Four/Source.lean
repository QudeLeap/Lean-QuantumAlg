/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Branch
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Block

/-!
# Source polynomial certificates for the initialized native branches

Positive-degree bounds use the original matching-parity synthesis theorem.
The zero-degree bound uses the polynomial's known constant coefficient,
without querying or inspecting the source unitary.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

private lemma exists_positive_branch {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) (degree : 0 < L) :
    ∃ phases : List ℝ, phases.length = L ∧
      ∀ (m n : Nat) (U : UnitaryOperator (Qubits (m + n)))
        (A : HilbertOperator (Qubits n)), ExactBlockEncoding m n U A → A.IsHermitian →
      projectedBlock m n (phasePlusBlock (initializedBranch U phases 1)) =
        polynomialOperator (realPolynomialToComplex P) A := by
  let certificate :=
    ReflectionQSPPhaseSynthesis.chooseRealBoundedPhaseCertificateOfSourceHypotheses source
  let phases := projectedPhasesFromQSPCertificate
    certificate.certificate.φ₀ certificate.certificate.φs
  have length : phases.length = L :=
    (projectedPhasesFromQSPCertificate_length _ _).trans certificate.certificate.length_eq
  refine ⟨phases, length, ?_⟩
  intro m n U A encoding hermitian
  have correct := Native.circuit_of_real_certificate U
    (OrthogonalProjector.zeroAncilla m n) (OrthogonalProjector.zeroAncilla m n)
    true certificate degree
  have expanded : projectedPhasePlusBlock (OrthogonalProjector.zeroAncilla m n)
      (OrthogonalProjector.zeroAncilla m n)
      ((Total.circuit (m := m) (n := n) true phases).binaryMatrix
        (UnitarySource.interpretation U true true false)) =
        singularValuePolynomial (OrthogonalProjector.zeroAncilla m n) L
          (realPolynomialToComplex P)
          (projectedUnitaryBlock (OrthogonalProjector.zeroAncilla m n)
            (OrthogonalProjector.zeroAncilla m n) U) := by
    rw [Total.totalCircuit_matrix]
    simpa only [projectedOutputProjector, ite_self] using correct
  have encoded := Total.totalZeroBlockCircuit_correct U true phases encoding hermitian
    (ReflectionQSPPhaseSynthesis.hasParity_realPolynomialToComplex source.parity) expanded
  have block := encoded.projected_block_eq
  rw [Total.totalZeroBlockCircuit_matrix, projectedBlock_reassociatedPhaseHadamardWrapper] at block
  simpa only [totalInitializedBranch_one] using block

/-- Polynomial-only branch data work for every encoding, including the constant boundary. -/
lemma exists_total_initialized_polynomial_branch {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ phases : List ℝ, ∃ constant : ℝ, phases.length = L ∧
      (0 < L → constant = 1) ∧
      ∀ (m n : Nat) (U : UnitaryOperator (Qubits (m + n)))
        (A : HilbertOperator (Qubits n)), ExactBlockEncoding m n U A → A.IsHermitian →
      projectedBlock m n (phasePlusBlock (initializedBranch U phases constant)) =
        polynomialOperator (realPolynomialToComplex P) A := by
  by_cases zero : L = 0
  · subst L
    have degree : P.natDegree = 0 := Nat.eq_zero_of_le_zero source.degree_le
    have constantPolynomial : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero degree
    have bound : |P.coeff 0| ≤ 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact source.bounded 0 (by constructor <;> norm_num)
    refine ⟨[], P.coeff 0, rfl, by omega, ?_⟩
    intro m n U A _encoding _hermitian
    have polynomial : polynomialOperator (realPolynomialToComplex P) A =
        (P.coeff 0 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
      rw [constantPolynomial]
      simp [realPolynomialToComplex, polynomialOperator_C]
    rw [totalInitializedBranch_constant_block U _ (abs_le.mp bound).1 (abs_le.mp bound).2]
    exact polynomial.symm
  · have degree : 0 < L := Nat.pos_of_ne_zero zero
    obtain ⟨phases, length, correct⟩ :=
      exists_positive_branch source degree
    exact ⟨phases, 1, length, fun _ => rfl, correct⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
