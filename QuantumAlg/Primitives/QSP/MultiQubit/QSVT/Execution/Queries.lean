/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Real
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Complex
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Queries
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Counts
import all QuantumAlg.Components.Gates.Toffoli.Refinement.Queries

/-!
# Source access of the uniform QSVT execution budgets

Degree zero performs no query. Positive matching-parity degree uses exactly L
ordinary or inverse queries; the complex construction uses at most L such
queries and one controlled forward query. Controlled inverse access is unused.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Execution
open Gate.Toffoli
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

private theorem realBudget_query (L : Nat) (coordinate : UnitarySource.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
      (.oracle coordinate) (realBudget U L) =
      if L = 0 then 0 else ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
        (.oracle coordinate) (KnownZero.Total.budget U false L) := by
  unfold realBudget
  split_ifs
  · simp
  · rw [expanded_query_count (UnitarySource.model U false true false) _ coordinate]
    simp

/-- Exactly L ordinary or inverse source accesses, including the degree-zero boundary. -/
theorem realBudget_source_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
      (.oracle UnitarySource.Coordinate.ordinary) (realBudget U L) +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
      (.oracle UnitarySource.Coordinate.inverse) (realBudget U L) = L := by
  rw [realBudget_query, realBudget_query]
  split_ifs with zero
  · omega
  · exact KnownZero.Total.totalRealBudget_source_queries U false L

/-- No controlled forward source access is used on the matching-parity route. -/
theorem realBudget_controlled_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
      (.oracle UnitarySource.Coordinate.controlled) (realBudget U L) = 0 := by
  rw [realBudget_query]
  split_ifs <;> simp [KnownZero.Total.totalRealBudget_controlled_queries]

/-- The matching-parity route never uses controlled inverse access. -/
theorem realBudget_controlled_inverse_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U false true false))
      (.oracle UnitarySource.Coordinate.controlledInverse) (realBudget U L) = 0 := by
  rw [realBudget_query]
  split_ifs <;> simp [KnownZero.Total.totalRealBudget_controlled_inverse_queries]

private theorem complexBudget_query (L : Nat) (coordinate : UnitarySource.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle coordinate) (complexBudget U L) =
      if L = 0 then 0 else ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
        (.oracle coordinate) (KnownZero.Total.Four.complexBudget U (L - 1)) := by
  unfold complexBudget
  split_ifs
  · simp
  · exact expanded_query_count (UnitarySource.model U true true false) _ coordinate

/-- Shared ordinary and inverse slots grow at most linearly in the original degree. -/
theorem complexBudget_source_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.ordinary) (complexBudget U L) +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.inverse) (complexBudget U L) ≤ L := by
  rw [complexBudget_query, complexBudget_query]
  split_ifs with zero
  · omega
  · have bound := KnownZero.Total.Four.totalComplexBudget_uncontrolled_queries_le U (L - 1)
    omega

/-- Positive degree uses one controlled forward query; degree zero uses none. -/
theorem complexBudget_controlled_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlled) (complexBudget U L) =
        if L = 0 then 0 else 1 := by
  rw [complexBudget_query]
  split_ifs <;> simp [KnownZero.Total.Four.totalComplexBudget_controlled_queries]

/-- The complex route never assumes controlled inverse access. -/
theorem complexBudget_controlled_inverse_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse) (complexBudget U L) = 0 := by
  rw [complexBudget_query]
  split_ifs <;> simp [KnownZero.Total.Four.totalComplexBudget_controlled_inverse_queries]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Execution
