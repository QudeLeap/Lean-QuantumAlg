/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Invariant
public import QuantumAlg.Components.Oracle.ProjectedSignal
public import QuantumAlg.Primitives.QSP.SingleQubit.PhaseSynthesis
import all QuantumAlg.Core.Algorithm.Unitary.Owned.Binary
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement

/-!
# Complete projected singular-value transformation

The original source and projector queries remain explicitly granted accesses.
The existential unitary implements the source projected polynomial block,
and its actual native word solves the independently budgeted complete-state
execution problem [GSLW19, BlockHam.tex:747-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
noncomputable section

/-- **Input.** One supplied owned phase qubit and the original N signal qubits.
**Output.** Every input system after the specified implementing unitary acts.
**Resource budget.** The independent degree-indexed source/projector query and rotation
budget, N+1 live qubits, and abstract depth at most 4 L+1.
**Success.** Exact full joint-state action with every external reference retained.
**Source.** Projected real singular-value transformation [GSLW19, BlockHam.tex:851]. -/
public def problem {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N) (L : Nat) (V : UnitaryOperator (Qubits (1 + N))) :=
  UnitaryExecution.Owned.Binary.problem V (Execution.projectedBudget U left right L) (4 * L + 1)

/-- Execute the actual projected word on its complete owned interface. -/
public def algorithm {N : Nat} (U : UnitaryOperator (Qubits N))
    (left right : OrthogonalProjector N)
    (word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right)
      (UnitaryExecution.Owned.Binary.layout (1 + N))) :=
  UnitaryExecution.Owned.Binary.algorithm word

/-- Every permitted degree has an actual complete execution of the source polynomial block. -/
public theorem main {N L : Nat} {P : Polynomial ℝ}
    (U : UnitaryOperator (Qubits N)) (left right : OrthogonalProjector N)
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L P) :
    ∃ V : UnitaryOperator (Qubits (1 + N)),
      projectedPhasePlusBlock (projectedOutputProjector left right L) right V =
        singularValuePolynomial right L (realPolynomialToComplex P)
          (projectedUnitaryBlock left right U) ∧
      ∃ word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right)
          (UnitaryExecution.Owned.Binary.layout (1 + N)),
        Algorithm.Solves (algorithm U left right word) (problem U left right L V) ∧
        word.binaryMatrix = V ∧
        word.eventCost = (problem U left right L V).resources.events := by
  obtain ⟨word, block, cost, depth⟩ := Execution.exists_projected_execution U left right source
  refine ⟨word.binaryMatrix, block, word, ?_, rfl, cost⟩
  exact UnitaryExecution.Owned.Binary.main word.binaryMatrix
    (Execution.projectedBudget U left right L) (4 * L + 1) word rfl (le_of_eq cost) depth

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
