/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Bounds
public import QuantumAlg.Components.Oracle.BlockEncoding
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Components.Oracle.SignalProcessing
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Queries
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Coordinates

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Real

/-!
# Complete real QSVT construction facts

The same execution has the source polynomial block, exact occurrence budget,
and all original native coordinate bounds. These stronger construction facts
are separate from the public existential execution interface.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianRealParity
noncomputable section

/-- The original polynomial assumptions yield a complete exact block-encoding execution. -/
public lemma realParity_complete_execution (m n : Nat) {L : Nat} {P : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) false true false)
        (UnitaryExecution.Owned.Binary.layout ((1 + m) + n)),
      Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word) (problem m n source) ∧
        word.eventCost = (problem m n source).resources.events ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.gate AlgorithmGate.Coordinate.singleQubit) word.eventCost +
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.gate AlgorithmGate.Coordinate.cnot) word.eventCost ≤
            15 * ((40 * m + 3) * L + 2) ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
          (.gate .toffoli) word.eventCost = 0 ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.oracle .ordinary) word.eventCost +
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.oracle .inverse) word.eventCost = L ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.oracle .controlled) word.eventCost = 0 ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.oracle .controlledInverse) word.eventCost = 0 ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.gate .cnot) word.eventCost ≤ 192 * m * L ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) false true false))
            (.gate .singleQubit) word.eventCost ≤ (296 * m + 3) * L + 2 ∧
      ∀ (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n)),
        ExactBlockEncoding m n U A → A.IsHermitian →
        ∃ V : UnitaryOperator (Qubits ((1 + m) + n)),
          ExactBlockEncoding (1 + m) n V (polynomialOperator (realPolynomialToComplex P) A) ∧
          word.binaryMatrix (UnitarySource.interpretation U false true false) = V := by
  obtain ⟨word, semantic, cost, depth, gates, toffoli⟩ :=
    Execution.Selected.exists_real_target_execution m n source
  refine ⟨word, ?_, cost, ?_, toffoli, ?_, ?_, ?_, ?_, ?_⟩
  · exact word_solves m n source word
      (fun U A encoding hermitian => (semantic U A encoding hermitian).1) cost depth
  · simpa only [Gate.Toffoli.nativeGateCount, toffoli, Nat.add_zero] using gates
  · rw [cost]
    exact Execution.realBudget_source_queries m n L
  · rw [cost]
    exact Execution.realBudget_controlled_queries m n L
  · rw [cost]
    exact Execution.realBudget_controlled_inverse_queries m n L
  · rw [cost]
    exact (Execution.realBudget_coordinate_bounds m n L).1
  · constructor
    · rw [cost]
      exact (Execution.realBudget_coordinate_bounds m n L).2
    · intro U A encoding hermitian
      exact ⟨_, (semantic U A encoding hermitian).2, rfl⟩

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianRealParity
