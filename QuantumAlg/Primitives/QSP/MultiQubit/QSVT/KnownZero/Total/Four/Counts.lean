/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Resources

/-!
# Explicit query coordinates of the shared source word

Four coherent phase branches use one common sequence of ordinary source
queries. Both controlled coordinates stay zero, even when controlled forward
access is available for a later unmatched parity slot.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
  (allowControlled : Bool)

private lemma phaseBudget_query_zero (coordinate : UnitarySource.Coordinate) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle coordinate) (phaseBudget (m := m) (n := n) allowControlled) = 0 := by
  have native (width : Nat) : ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle coordinate)
      (ZeroProjector.SourceWork.budget (UnitarySource.model (m + n) allowControlled true false)
        width) =
        0 := by
    unfold ZeroProjector.SourceWork.budget
    split_ifs <;> simp
  cases n <;> cases m <;> simp [phaseBudget, nativePhaseBudget, native]

/-- Ordinary source queries occur once per odd-numbered source slot, shared by all four branches. -/
lemma totalFourWord_ordinary_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.ordinary)
      (circuit (m := m) (n := n) allowControlled phases).eventCost = (phases.length + 1) / 2 := by
  rw [totalFourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- Inverse queries occupy the even-numbered shared slots and remain separately counted. -/
lemma totalFourWord_inverse_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.inverse)
      (circuit (m := m) (n := n) allowControlled phases).eventCost = phases.length / 2 := by
  rw [totalFourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- A common source sequence never turns ordinary queries into controlled queries. -/
lemma totalFourWord_controlled_queries_zero (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.controlled)
      (circuit (m := m) (n := n) allowControlled phases).eventCost = 0 := by
  rw [totalFourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

/-- No controlled-inverse access is present or silently introduced. -/
lemma totalFourWord_controlled_inverse_queries_zero (phases : List ((ℝ × ℝ) × (ℝ × ℝ))) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.controlledInverse)
      (circuit (m := m) (n := n) allowControlled phases).eventCost = 0 := by
  rw [totalFourWord_events]
  simp [budget, eventPool, phaseBudget_query_zero]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
