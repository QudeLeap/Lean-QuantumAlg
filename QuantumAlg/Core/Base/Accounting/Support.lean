/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Coordinatewise budgets from finite support and event cardinality

A cardinality bound alone does not determine a resource pool. Once every
actual event is proved to belong to an independent finite alphabet, scaling
that alphabet by the cardinality bound dominates each native coordinate.
-/

namespace QuantumAlg.ResourcePool

/-- Finite support and total cardinality together imply the scaled coordinatewise bound. -/
lemma le_scaled_of_support_card_le {model : ExecutionModel}
    (pool alphabet : ResourcePool model) (bound : Nat)
    (supported : ∀ focus ∈ pool, focus ∈ alphabet) (bounded : pool.card ≤ bound) :
    pool ≤ bound • alphabet := by
  apply ResourcePool.le_iff_count.mpr
  intro focus
  by_cases present : focus ∈ alphabet
  · rw [ResourcePool.count_nsmul]
    have positive : 1 ≤ ResourcePool.count focus alphabet :=
      Multiset.one_le_count_iff_mem.mpr present
    have countBound : ResourcePool.count focus pool ≤ bound :=
      (Multiset.count_le_card focus pool).trans bounded
    have budgetBound := Nat.mul_le_mul_left bound positive
    omega
  · have absent : focus ∉ pool := fun membership => present (supported focus membership)
    have zero : ResourcePool.count focus pool = 0 := Multiset.count_eq_zero.mpr absent
    rw [zero]
    exact Nat.zero_le _

end QuantumAlg.ResourcePool
