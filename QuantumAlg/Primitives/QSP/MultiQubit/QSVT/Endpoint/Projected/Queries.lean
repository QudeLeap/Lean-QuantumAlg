/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Decomposition

/-!
# Exact access counts of complete projected QSVT execution

The source-unitary accesses and the two projector accesses remain distinct
coordinates. All counts follow from the same actual word's event equality.
Degree zero has one native gate and no query of any kind.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
noncomputable section

variable {N L : Nat} (U : UnitaryOperator (Qubits N))
  (left right : OrthogonalProjector N) (V : UnitaryOperator (Qubits (1 + N)))
  (word : UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right)
    (UnitaryExecution.Owned.Binary.layout (1 + N)))
  (cost : word.eventCost = (problem U left right L V).resources.events)

include cost

/-- Exactly L ordinary or inverse accesses to the original source operator. -/
public theorem projectedEndpoint_source_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle (.source .ordinary)) word.eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle (.source .inverse)) word.eventCost = L := by
  have actual : word.eventCost = Execution.projectedBudget U left right L := cost
  rw [actual]
  by_cases zero : L = 0
  · subst L
    simp [Execution.projectedBudget]
  · simp only [Execution.projectedBudget, zero, ↓reduceIte]
    exact Native.Balanced.budget_source_queries U left right false L

/-- Exactly L calls to the input projector-controlled NOT. -/
public theorem projectedEndpoint_right_projector_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle .rightNot) word.eventCost = L := by
  have actual : word.eventCost = Execution.projectedBudget U left right L := cost
  rw [actual]
  by_cases zero : L = 0
  · subst L
    simp [Execution.projectedBudget]
  · simp only [Execution.projectedBudget, zero, ↓reduceIte]
    exact Native.Balanced.budget_right_projector_queries U left right false L

/-- Exactly L calls to the output-projector family, including odd degree. -/
public theorem projectedEndpoint_left_projector_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle .leftNot) word.eventCost = L := by
  have actual : word.eventCost = Execution.projectedBudget U left right L := cost
  rw [actual]
  by_cases zero : L = 0
  · subst L
    simp [Execution.projectedBudget]
  · simp only [Execution.projectedBudget, zero, ↓reduceIte]
    exact Native.Balanced.budget_left_projector_queries U left right false L

/-- The two projector families contribute exactly 2L calls in total. -/
public theorem projectedEndpoint_projector_queries :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle .leftNot) word.eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.oracle .rightNot) word.eventCost = 2 * L := by
  have actual : word.eventCost = Execution.projectedBudget U left right L := cost
  rw [actual]
  by_cases zero : L = 0
  · subst L
    simp [Execution.projectedBudget]
  · simp only [Execution.projectedBudget, zero, ↓reduceIte]
    rw [Native.Balanced.budget_left_projector_queries,
      Native.Balanced.budget_right_projector_queries]
    omega

/-- The native rotation count includes the single degree-zero dilation. -/
public theorem projectedEndpoint_single_qubit_count :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (ProjectedSignal.model U left right))
      (.gate .singleQubit) word.eventCost = max 1 L := by
  have actual : word.eventCost = Execution.projectedBudget U left right L := cost
  rw [actual]
  by_cases zero : L = 0
  · subst L
    simp [Execution.projectedBudget]
  · simp only [Execution.projectedBudget, zero, ↓reduceIte]
    rw [Native.Balanced.budget_single_qubit_count]
    omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.Witness.Projected
