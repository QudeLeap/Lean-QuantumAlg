/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution

/-!
# Query counts of the complete four-branch native execution

Constant initialization, relative phase and all six boundary Hadamards are
native operations. They do not multiply or conceal any source query slot.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

/-- The independent complete budget permits precisely one controlled forward query. -/
lemma totalComplexBudget_controlled_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlled) (complexBudget (m := m) (n := n) L) = 1 := by
  unfold complexBudget unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- The complete budget never assumes controlled inverse access. -/
lemma totalComplexBudget_controlled_inverse_queries (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.controlledInverse) (complexBudget (m := m) (n := n) L)
        = 0 := by
  unfold complexBudget unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero]

/-- Ordinary and inverse query slots together are bounded by the longer branch length. -/
lemma totalComplexBudget_uncontrolled_queries_le (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.ordinary) (complexBudget (m := m) (n := n) L) +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
      (.oracle UnitarySource.Coordinate.inverse) (complexBudget (m := m) (n := n) L) ≤ L + 1 := by
  unfold complexBudget unmatchedBudget
  split_ifs <;> simp [budget, eventPool, phaseBudget_query_zero] <;> omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
