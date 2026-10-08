/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Certificate
import all QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis

/-!
# Actual degree-zero matching-parity execution

The original real interval bound supplies one native scalar dilation. It uses
one transformation ancilla and one single-qubit gate, and does not query the
source operator. No positivity assumption on either source width is needed.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Scalar
noncomputable section

/-- Real interval boundedness implies the complex norm-square bound used by scalar dilation. -/
theorem real_polynomial_normSq_bound {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      Complex.normSq ((realPolynomialToComplex P).eval (x : ℂ)) ≤ 1 := by
  intro x interval
  rw [realPolynomialToComplex_eval_ofReal, Complex.normSq_ofReal]
  simpa only [pow_two] using (sq_le_one_iff_abs_le_one (P.eval x)).mpr
    (source.bounded x interval)

/-- Degree zero retains the original normalization, one ancilla, and zero source queries. -/
theorem exists_real_constant_execution {m n : Nat} (oracles : OracleModel)
    (P : Polynomial ℝ) (A : HilbertOperator (Qubits n))
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity 0 P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model oracles (layout m n),
      ExactBlockEncoding (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n) word.binaryMatrix)
        (polynomialOperator (realPolynomialToComplex P) A) ∧
      word.eventCost = ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) ∧
      word.evaluatedEventDepth (fun _ => 1) = 1 := by
  let polynomial := realPolynomialToComplex P
  have bounded := real_polynomial_normSq_bound source
  have degree : polynomial.natDegree = 0 := by
    rw [realPolynomialToComplex_natDegree]
    exact Nat.eq_zero_of_le_zero source.degree_le
  refine ⟨circuit oracles m n (polynomial.coeff 0)
    (constant_coefficient_bound polynomial bounded), ?_, rfl, rfl⟩
  exact scalarCircuit_constant_polynomial oracles polynomial A degree bounded

end
end QuantumAlg.QSP.MultiQubit.QSVT.Scalar
