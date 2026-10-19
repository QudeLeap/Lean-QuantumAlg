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
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Queries
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Coordinates

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Selected.Complex

/-!
# Complete complex QSVT construction facts

The same execution has the source polynomial block, exact occurrence budget,
and all original native coordinate bounds. These stronger construction facts
are separate from the public existential execution interface.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
noncomputable section

/-- The original polynomial assumptions yield a complete exact block-encoding execution. -/
public lemma complex_complete_execution (m n : Nat) {L : Nat}
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model (m + n) true true false)
        (UnitaryExecution.Owned.Binary.layout (Execution.Selected.complexAncillas m L + n)),
      m ≤ Execution.Selected.complexAncillas m L ∧
      Execution.Selected.complexAncillas m L ≤ m + 3 ∧
      Algorithm.Solves (UnitaryExecution.Owned.Binary.algorithm word)
        (problem m n P degree bounded) ∧
        word.eventCost = (problem m n P degree bounded).resources.events ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.gate AlgorithmGate.Coordinate.singleQubit) word.eventCost +
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.gate AlgorithmGate.Coordinate.cnot) word.eventCost ≤
            15 * ((40 * m + 20) * L + 19) ∧
        ResourcePool.count
          (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
          (.gate .toffoli) word.eventCost = 0 ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.oracle .ordinary) word.eventCost +
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.oracle .inverse) word.eventCost ≤ L ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.oracle .controlled) word.eventCost = (if L = 0 then 0 else 1) ∧
        ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.oracle .controlledInverse) word.eventCost = 0 ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.gate .cnot) word.eventCost ≤ (192 * m + 6) * L + 6 ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
            (.gate .singleQubit) word.eventCost ≤ (296 * m + 6) * L + 13 ∧
      ∀ (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n)),
        ExactBlockEncoding m n U A → A.IsHermitian →
        ∃ V : UnitaryOperator (Qubits (Execution.Selected.complexAncillas m L + n)),
          ExactBlockEncoding (Execution.Selected.complexAncillas m L) n V
            ((1 / 4 : ℂ) • polynomialOperator P A) ∧
          word.binaryMatrix (UnitarySource.interpretation U true true false) = V := by
  obtain ⟨word, semantic, cost, depth, gates, toffoli⟩ :=
    Execution.Selected.exists_complex_target_execution m n P degree bounded
  have width := Execution.Selected.complexTarget_width m L
  have lower : m ≤ Execution.Selected.complexAncillas m L := by
    rw [width]; split_ifs <;> omega
  have upper : Execution.Selected.complexAncillas m L ≤ m + 3 := by
    rw [width]; split_ifs <;> omega
  refine ⟨word, lower, upper, ?_, cost, ?_, toffoli, ?_, ?_, ?_, ?_, ?_⟩
  · exact word_solves m n P degree bounded word semantic cost depth
  · simpa only [Gate.Toffoli.nativeGateCount, toffoli, Nat.add_zero] using gates
  · rw [cost]
    exact Execution.complexBudget_source_queries m n L
  · rw [cost]
    exact Execution.complexBudget_controlled_queries m n L
  · rw [cost]
    exact Execution.complexBudget_controlled_inverse_queries m n L
  · rw [cost]
    exact (Execution.complexBudget_coordinate_bounds m n L).1
  · constructor
    · rw [cost]
      exact (Execution.complexBudget_coordinate_bounds m n L).2
    · intro U A encoding hermitian
      exact ⟨_, Execution.Selected.complexTarget_block U A encoding hermitian P degree bounded,
        semantic U⟩


end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
