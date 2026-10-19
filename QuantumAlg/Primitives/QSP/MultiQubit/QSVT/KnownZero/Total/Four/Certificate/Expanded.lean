/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Certificate.Execution
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Queries
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Depth
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Complex QSVT executed using single-qubit gates, CNOTs and source queries

The Toffoli expansion retains the same physical layout and full operator.
Its complete event pool and depth come from the actual substituted word, with
no residual Toffoli operation and no additional source access.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

/-- Positive-degree complex QSVT admits an actual one- and two-qubit native execution. -/
lemma exists_total_complex_expanded_execution {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n)))
    (A : HilbertOperator (Qubits n)) (encoding : ExactBlockEncoding m n U A)
    (hermitian : A.IsHermitian) (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (positiveDegree : 0 < L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model
        (UnitarySource.model (m + n) true true false) (layout m n),
      ExactBlockEncoding (1 + (1 + (1 + m))) n (reassociateThree (circuit.binaryMatrix
        (UnitarySource.interpretation U true true false)))
        ((1 / 4 : ℂ) • polynomialOperator P A) ∧
      circuit.eventCost = Gate.Toffoli.expandedBudget
        (UnitarySource.model (m + n) true true false) (complexBudget (m := m) (n := n) (L - 1)) ∧
      circuit.evaluatedEventDepth (fun _ => 1) ≤ 15 * ((40 * m + 21) * L + 20) ∧
      Gate.Toffoli.nativeGateCount circuit.eventCost ≤
        15 * ((40 * m + 20) * L + 19) ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
        (.gate .toffoli) circuit.eventCost = 0 := by
  obtain ⟨source, block, budget, depth⟩ := exists_total_complex_native_execution
    U A encoding hermitian P degree positiveDegree bounded
  refine ⟨Gate.Toffoli.expand source, ?_, ?_, ?_, ?_,
    Gate.Toffoli.toffoliExpansion_expanded_toffoli_count source⟩
  · have same : ((Gate.Toffoli.expand source).binaryMatrix
    (UnitarySource.interpretation U true true false))
    = (source.binaryMatrix (UnitarySource.interpretation U true true false)) := by
      unfold UnitaryCircuit.binaryMatrix
      rw [Gate.Toffoli.toffoliExpansion_preserves_matrix]
    rw [same]
    exact block
  · rw [Gate.Toffoli.toffoliExpansion_expanded_eventCost, budget]
  · exact (Gate.Toffoli.toffoliExpansion_depth_le source).trans
      (Nat.mul_le_mul_left 15 depth)
  · have nativeBound := totalComplexBudget_native_gate_bound (m := m) (n := n) (L - 1)
    rw [Nat.sub_add_cancel positiveDegree] at nativeBound
    exact (Gate.Toffoli.toffoliExpansion_native_gate_bound source).trans
      (Nat.mul_le_mul_left 15 (by simpa only [budget] using nativeBound))

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
