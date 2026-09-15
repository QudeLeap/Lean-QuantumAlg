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
public def weightedCount {kind : ProblemKind} (weight : Resource.Event kind → Nat)
    (pool : ResourcePool kind) : Nat :=
  (pool.map weight).sum

@[simp] theorem weightedCount_zero {kind : ProblemKind}
    (weight : Resource.Event kind → Nat) :
    weightedCount weight (0 : ResourcePool kind) = 0 := by
  simp [weightedCount]

@[simp] theorem weightedCount_add {kind : ProblemKind}
    (weight : Resource.Event kind → Nat)
    (left right : ResourcePool kind) :
    weightedCount weight (left + right) =
      weightedCount weight left + weightedCount weight right := by
  simp [weightedCount]

@[simp] theorem weightedCount_singleton {kind : ProblemKind}
    (weight : Resource.Event kind → Nat)
    (event : Resource.Event kind) (multiplicity : Nat) :
    weightedCount weight (ResourcePool.singleton event multiplicity) =
      multiplicity * weight event := by
  simp [weightedCount, ResourcePool.singleton]

@[simp] theorem weightedCount_nsmul {kind : ProblemKind}
    (weight : Resource.Event kind → Nat)
    (multiplicity : Nat) (pool : ResourcePool kind) :
    weightedCount weight (multiplicity • pool) =
      multiplicity * weightedCount weight pool := by
  induction multiplicity with
  | zero => simp
  | succ multiplicity ih =>
      rw [succ_nsmul, weightedCount_add, ih]
      simp [Nat.succ_mul]

@[simp] theorem weightedCount_ofList {kind : ProblemKind}
    (weight : Resource.Event kind → Nat)
    (events : List (Resource.Event kind)) :
    weightedCount weight (ResourcePool.ofList events) =
      (events.map weight).sum := by
  simp [weightedCount, ResourcePool.ofList]

end QuantumAlg.ResourcePool
