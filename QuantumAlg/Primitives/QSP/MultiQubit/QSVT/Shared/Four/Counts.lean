/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Resources

/-!
# Explicit query coordinates of the shared source word

Four coherent phase branches use one common sequence of ordinary source
queries. Both controlled coordinates stay zero, even when controlled forward
access is available for a later unmatched parity slot.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (positive : 0 < n) (allowControlled : Bool)

private theorem phaseBudget_query_zero (coordinate : UnitarySource.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))
      (.oracle coordinate) (phaseBudget U allowControlled) = 0 := by
  unfold phaseBudget ZeroProjector.SourceWork.budget
  split_ifs <;> simp [eventPool]

/-- Ordinary source queries occur once per odd-numbered source slot, shared by all four branches. -/
theorem fourWord_ordinary_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))
      (.oracle UnitarySource.Coordinate.ordinary)
      (circuit U positive allowControlled phases).eventCost = (phases.length + 1) / 2 := by
  rw [fourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- Inverse queries occupy the even-numbered shared slots and remain separately counted. -/
theorem fourWord_inverse_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))
      (.oracle UnitarySource.Coordinate.inverse)
      (circuit U positive allowControlled phases).eventCost = phases.length / 2 := by
  rw [fourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- A common source sequence never turns ordinary queries into controlled queries. -/
theorem fourWord_controlled_queries_zero (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))
      (.oracle UnitarySource.Coordinate.controlled)
      (circuit U positive allowControlled phases).eventCost = 0 := by
  rw [fourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- No controlled-inverse access is present or silently introduced. -/
theorem fourWord_controlled_inverse_queries_zero (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U allowControlled true false))
      (.oracle UnitarySource.Coordinate.controlledInverse)
      (circuit U positive allowControlled phases).eventCost = 0 := by
  rw [fourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
