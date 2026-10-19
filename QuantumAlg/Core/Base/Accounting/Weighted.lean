/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Weighted sums over native event ledgers

Weights observe the literal event coordinates already present in a pool. They
do not expand gates or certify a physical implementation of a different basis.
The same operations apply to classical and quantum execution events.
-/

namespace QuantumAlg.ResourcePool

/-- Sum a natural-number event weight over a strict resource ledger. -/
public def weightedCount {model : ExecutionModel} (weight : Resource.Event model → Nat)
    (pool : ResourcePool model) : Nat :=
  (pool.map weight).sum

@[simp] lemma weightedCount_zero {model : ExecutionModel}
    (weight : Resource.Event model → Nat) :
    weightedCount weight (0 : ResourcePool model) = 0 := by
  simp [weightedCount]

/-- A ledger has zero total weight when every event it actually contains has zero weight. -/
lemma weightedCount_eq_zero_of_mem {model : ExecutionModel}
    (weight : Resource.Event model → Nat) (pool : ResourcePool model)
    (zero : ∀ event ∈ pool, weight event = 0) : weightedCount weight pool = 0 := by
  revert zero
  induction pool using Multiset.induction_on with
  | empty => intro _; rfl
  | cons event rest ih =>
      intro zero
      have eventZero : weight event = 0 := zero event (by simp)
      have restZero : ∀ other ∈ rest, weight other = 0 := by
        intro other present
        exact zero other (by simp [present])
      simpa only [weightedCount, Multiset.map_cons, Multiset.sum_cons,
        eventZero, Nat.zero_add] using ih restZero

@[simp] lemma weightedCount_add {model : ExecutionModel}
    (weight : Resource.Event model → Nat)
    (left right : ResourcePool model) :
    weightedCount weight (left + right) =
      weightedCount weight left + weightedCount weight right := by
  simp [weightedCount]

@[simp] lemma weightedCount_singleton {model : ExecutionModel}
    (weight : Resource.Event model → Nat)
    (event : Resource.Event model) (multiplicity : Nat) :
    weightedCount weight (ResourcePool.singleton event multiplicity) =
      multiplicity * weight event := by
  simp [weightedCount, ResourcePool.singleton]

@[simp] lemma weightedCount_nsmul {model : ExecutionModel}
    (weight : Resource.Event model → Nat)
    (multiplicity : Nat) (pool : ResourcePool model) :
    weightedCount weight (multiplicity • pool) =
      multiplicity * weightedCount weight pool := by
  induction multiplicity with
  | zero => simp
  | succ multiplicity ih =>
      rw [succ_nsmul, weightedCount_add, ih]
      simp [Nat.succ_mul]

@[simp] lemma weightedCount_ofList {model : ExecutionModel}
    (weight : Resource.Event model → Nat)
    (events : List (Resource.Event model)) :
    weightedCount weight (ResourcePool.ofList events) =
      (events.map weight).sum := by
  simp [weightedCount, ResourcePool.ofList]

end QuantumAlg.ResourcePool
