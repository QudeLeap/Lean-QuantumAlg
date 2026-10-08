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

/-!
# Complete complex Hermitian polynomial transformation

The source statement is existential in the implementing block-encoding
unitary [GSLW19, BlockHam.tex:1938]. The target unitary is a parameter of the
independent execution problem; synthesis supplies a unitary satisfying the
required polynomial block and an actual circuit solving that problem.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
noncomputable section

/-- **Input.** A supplied owned register of a block ancillas and n system qubits.
**Output.** The same register transformed by the specified block-encoding unitary.
**Resource budget.** Degree/width native budget, a+n live qubits, and
15 ((40 m+21) L+20) abstract depth, including source queries.
**Success.** Exact action on arbitrary joint inputs and external references.
**Source.** Complex polynomial transformation [GSLW19, BlockHam.tex:1938]. -/
public def problem {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (L : Nat)
    {a : Nat} (V : UnitaryOperator (Qubits (a + n))) :=
  UnitaryExecution.Owned.Binary.problem V (Execution.complexBudget U L)
      (15 * ((40 * m + 21) * L + 20))

/-- Run the synthesized native construction on its entire owned input interface. -/
public def algorithm {m n a : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false)
      (UnitaryExecution.Owned.Binary.layout (a + n))) :=
  UnitaryExecution.Owned.Binary.algorithm word

/-- The original polynomial assumptions yield a complete exact block-encoding execution. -/
public theorem main {m n L : Nat}
    (U : UnitaryOperator (Qubits (m + n))) (A : HilbertOperator (Qubits n))
    (encoding : ExactBlockEncoding m n U A) (hermitian : A.IsHermitian)
    (P : Polynomial ℂ) (degree : P.natDegree ≤ L)
    (bounded : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → Complex.normSq (P.eval (x : ℂ)) ≤ 1) :
    ∃ a : Nat, m ≤ a ∧ a ≤ m + 3 ∧
      ∃ V : UnitaryOperator (Qubits (a + n)),
        ExactBlockEncoding a n V ((1 / 4 : ℂ) • polynomialOperator P A) ∧
        ∃ word : UnitaryCircuit AlgorithmGate.model (UnitarySource.model U true true false)
            (UnitaryExecution.Owned.Binary.layout (a + n)),
          Algorithm.Solves (algorithm U word) (problem U L V) ∧
          word.binaryMatrix = V ∧
          word.eventCost = (problem U L V).resources.events ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
            (.gate AlgorithmGate.Coordinate.singleQubit) word.eventCost +
            ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
            (.gate AlgorithmGate.Coordinate.cnot) word.eventCost ≤
            15 * ((40 * m + 20) * L + 19) ∧
          ResourcePool.count
            (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
            (.gate .toffoli) word.eventCost = 0 ∧
          ResourcePool.count
              (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
              (.oracle .ordinary) word.eventCost +
            ResourcePool.count
              (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
              (.oracle .inverse) word.eventCost ≤ L ∧
          ResourcePool.count
              (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
              (.oracle .controlled) word.eventCost = (if L = 0 then 0 else 1) ∧
          ResourcePool.count
              (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
              (.oracle .controlledInverse) word.eventCost = 0 := by
  obtain ⟨a, lower, upper, word, block, cost, depth, gates, toffoli⟩ :=
    Execution.exists_complex_execution U A encoding hermitian P degree bounded
  refine ⟨a, lower, upper, word.binaryMatrix, block, word, ?_, rfl, cost, ?_,
    toffoli, ?_, ?_, ?_⟩
  · exact UnitaryExecution.Owned.Binary.main word.binaryMatrix (Execution.complexBudget U L)
      (15 * ((40 * m + 21) * L + 20)) word rfl (le_of_eq cost) depth
  · simpa only [Gate.Toffoli.nativeGateCount, toffoli, Nat.add_zero] using gates
  · rw [cost]
    exact Execution.complexBudget_source_queries U L
  · rw [cost]
    exact Execution.complexBudget_controlled_queries U L
  · rw [cost]
    exact Execution.complexBudget_controlled_inverse_queries U L

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.HermitianComplex
