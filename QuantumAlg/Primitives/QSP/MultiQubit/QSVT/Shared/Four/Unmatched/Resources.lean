/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Unmatched
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Counts

/-!
# Actual resources of the four-branch unmatched parity slot

There is exactly one controlled forward query, independently of degree. An
even final slot also uses one ordinary inverse and two native selector flips.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
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
theorem fourUnmatched_events (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (unmatched U positive phases realAngle imaginaryAngle).eventCost =
      unmatchedBudget U phases.length := by
  rw [unmatched, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    fourWord_events, fourPhase_events, lastSignal,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    UnitarySource.Conditional.withSpectator_events]
  by_cases even : (phases.length + 1) % 2 = 0
  · simp only [even, decide_true, ↓reduceIte, UnitarySource.Conditional.inverse_events,
      unmatchedBudget, eventPool]
    ac_rfl
  · simp only [even, decide_false, Bool.false_eq_true, ↓reduceIte, unmatchedBudget, add_zero]
    rfl

/-- Exactly one controlled forward access remains regardless of the common sequence length. -/
theorem fourUnmatched_controlled_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlled)
      (unmatched U positive phases realAngle imaginaryAngle).eventCost = 1 := by
  rw [fourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Expanded inverse control does not consume an ungranted controlled-inverse coordinate. -/
theorem fourUnmatched_controlled_inverse_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse)
      (unmatched U positive phases realAngle imaginaryAngle).eventCost = 0 := by
  rw [fourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Ordinary and inverse accesses together never exceed the longer branch length. -/
theorem fourUnmatched_uncontrolled_queries_le (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.ordinary)
      (unmatched U positive phases realAngle imaginaryAngle).eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model U true true false))
      (.oracle UnitarySource.Coordinate.inverse)
      (unmatched U positive phases realAngle imaginaryAngle).eventCost ≤ phases.length + 1 := by
  rw [fourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero] <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
