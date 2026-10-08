/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Counts

/-!
# Actual resources of the unmatched parity slot

There is exactly one controlled forward query, independently of degree. An
even final slot also uses one ordinary inverse and two native selector flips.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- Independent final-slot budget retains the physical inverse-control implementation. -/
def unmatchedBudget (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (UnitarySource.model U true true false)) :=
  budget U true L + eventPool U true (.oracle .controlled) +
    (if (L + 1) % 2 = 0 then
      eventPool U true (.oracle .inverse) + 2 • eventPool U true (.gate .singleQubit)
    else 0) + phaseBudget U true

/-- The complete resource pool is derived from the executed word, including both projector flips. -/
theorem unmatched_events (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    (unmatched U positive phases lastAngle).eventCost = unmatchedBudget U phases.length := by
  rw [unmatched, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    circuit_events, phase_events, UnitarySource.Conditional.withSpectator_events]
  by_cases even : (phases.length + 1) % 2 = 0
  · simp only [even, decide_true, ↓reduceIte, UnitarySource.Conditional.inverse_events,
      unmatchedBudget, eventPool]
    ac_rfl
  · simp only [even, decide_false, Bool.false_eq_true, ↓reduceIte, unmatchedBudget, add_zero]
    rfl

/-- Exactly one controlled forward access remains regardless of the common sequence length. -/
theorem unmatched_controlled_queries (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlled)
      (unmatched U positive phases lastAngle).eventCost = 1 := by
  rw [unmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Expanded inverse control does not consume an ungranted controlled-inverse coordinate. -/
theorem unmatched_controlled_inverse_queries (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse)
      (unmatched U positive phases lastAngle).eventCost = 0 := by
  rw [unmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Ordinary and inverse accesses together never exceed the longer branch length. -/
theorem unmatched_uncontrolled_queries_le (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.ordinary)
      (unmatched U positive phases lastAngle).eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.inverse)
      (unmatched U positive phases lastAngle).eventCost ≤ phases.length + 1 := by
  rw [unmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero] <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
