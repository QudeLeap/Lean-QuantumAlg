/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Scalar.Certificate

/-!
# Normalization-four constant polynomial execution

The degree-zero boundary uses one known single-qubit dilation and one
transformation ancilla. The original source and signal wires are untouched,
and no ordinary, inverse or controlled source query is introduced.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Scalar
noncomputable section

private lemma quarter_coefficient_bound (P : Polynomial ℂ)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    Complex.normSq ((1 / 4 : ℂ) * P.coeff 0) ≤ 1 := by
  have bound := constant_coefficient_bound P bounded
  have quarter : Complex.normSq (1 / 4 : ℂ) = (1 / 16 : ℝ) := by
    norm_num [Complex.normSq]
  rw [Complex.normSq_mul, quarter]
  nlinarith

/-- One actual gate realizes the normalized complex constant with its full resource pool. -/
lemma exists_normalized_constant_execution {m n : Nat} (oracles : OracleModel)
    (P : Polynomial ℂ) (A : HilbertOperator (Qubits n)) (degree : P.natDegree = 0)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : UnitaryCircuit AlgorithmGate.model oracles (layout m n),
      (∀ environment : oracles.Interpretation, ExactBlockEncoding (1 + m) n
        (reassociatePhaseAncillaOperator (m := m) (n := n) (word.binaryMatrix environment))
        ((1 / 4 : ℂ) • polynomialOperator P A)) ∧
      word.eventCost = ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) ∧
      word.evaluatedEventDepth (fun _ => 1) = 1 := by
  refine ⟨circuit oracles m n ((1 / 4 : ℂ) * P.coeff 0)
    (quarter_coefficient_bound P bounded), ?_, rfl, rfl⟩
  intro environment
  rw [circuit_source_matrix,
    polynomialOperator_eq_scalar_one_of_natDegree_eq_zero P A degree, smul_smul]
  exact exactBlockEncoding_scalarDilationWithSourceAncillas _ _

end
end QuantumAlg.QSP.MultiQubit.QSVT.Scalar
