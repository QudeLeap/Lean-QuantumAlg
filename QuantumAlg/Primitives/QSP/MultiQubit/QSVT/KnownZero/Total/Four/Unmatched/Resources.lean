/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Unmatched
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Counts

/-!
# Actual resources of the four-branch unmatched parity slot

There is exactly one controlled forward query, independently of degree. An
even final slot also uses one ordinary inverse and two native selector flips.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

/-- Independent final-slot budget retains the physical inverse-control implementation. -/
def unmatchedBudget (L : Nat) :
    ResourcePool (.quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false)) :=
  budget (m := m) (n := n) true L + eventPool (m := m) (n := n) true (.oracle .controlled) +
    (if (L + 1) % 2 = 0 then
      eventPool (m := m) (n := n) true (.oracle .inverse) + 2 • eventPool (m := m) (n := n) true
        (.gate .singleQubit)
    else 0) + phaseBudget (m := m) (n := n) true

/-- The complete resource pool is derived from the executed word, including both projector flips. -/
lemma totalFourUnmatched_events (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).eventCost =
      unmatchedBudget (m := m) (n := n) phases.length := by
  rw [unmatched, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    totalFourWord_events, totalFourPhase_events, SharedFour.lastSignal,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost,
    UnitarySource.Conditional.withSpectator_events]
  by_cases even : (phases.length + 1) % 2 = 0
  · simp only [even, decide_true, ↓reduceIte, UnitarySource.Conditional.inverse_events,
      unmatchedBudget, eventPool]
    ac_rfl
  · simp only [even, decide_false, Bool.false_eq_true, ↓reduceIte, unmatchedBudget, add_zero]
    rfl

/-- Exactly one controlled forward access remains regardless of the common sequence length. -/
lemma totalFourUnmatched_controlled_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlled)
      (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).eventCost = 1 := by
  rw [totalFourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Expanded inverse control does not consume an ungranted controlled-inverse coordinate. -/
lemma totalFourUnmatched_controlled_inverse_queries (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse)
      (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).eventCost = 0 := by
  rw [totalFourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Ordinary and inverse accesses together never exceed the longer branch length. -/
lemma totalFourUnmatched_uncontrolled_queries_le (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle : ℝ) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.ordinary)
      (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).eventCost +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.inverse)
      (unmatched (m := m) (n := n) phases realAngle imaginaryAngle).eventCost ≤ phases.length + 1
        := by
  rw [totalFourUnmatched_events]
  unfold unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero] <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
