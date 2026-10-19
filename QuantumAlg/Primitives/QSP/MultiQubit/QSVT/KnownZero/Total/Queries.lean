/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Counts

/-!
# Exact query counts of the all-width matching-parity word

Every known-projector phase is native. The only queries are the alternating
ordinary and inverse source slots, whose total is exactly the phase-list length.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
noncomputable section

private lemma phaseBudget_query_zero (m n : Nat) (oracles : OracleModel)
    (coordinate : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle coordinate)
      (phaseBudget m n oracles) = 0 := by
  have native (width : Nat) :
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle coordinate)
        (ZeroProjector.SourceWork.budget oracles width) = 0 := by
    unfold ZeroProjector.SourceWork.budget
    split_ifs <;> simp
  cases n <;> cases m <;> simp [phaseBudget, native]

/-- Exactly L source queries occur, counting ordinary and inverse access separately. -/
lemma totalRealBudget_source_queries {m n : Nat}
    (allowControlled : Bool) (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.ordinary) (budget (m := m) (n := n) allowControlled L) +
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.inverse) (budget (m := m) (n := n) allowControlled L)
        = L := by
  simp [budget, eventPool,
    phaseBudget_query_zero m n (UnitarySource.model (m + n) allowControlled true false) .ordinary,
    phaseBudget_query_zero m n (UnitarySource.model (m + n) allowControlled true false) .inverse]
  omega

/-- Known-projector expansion introduces no controlled source query. -/
lemma totalRealBudget_controlled_queries {m n : Nat}
    (allowControlled : Bool) (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.controlled) (budget (m := m) (n := n) allowControlled L)
        = 0 := by
  simp [budget, eventPool,
    phaseBudget_query_zero m n (UnitarySource.model (m + n) allowControlled true false) .controlled]

/-- No controlled inverse access is used by the actual matching-parity word. -/
lemma totalRealBudget_controlled_inverse_queries {m n : Nat}
    (allowControlled : Bool) (L : Nat) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) allowControlled true
        false))
      (.oracle UnitarySource.Coordinate.controlledInverse) (budget (m := m) (n := n)
        allowControlled L) = 0 := by
  simp [budget, eventPool,
    phaseBudget_query_zero m n (UnitarySource.model (m + n) allowControlled true false)
      .controlledInverse]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total
