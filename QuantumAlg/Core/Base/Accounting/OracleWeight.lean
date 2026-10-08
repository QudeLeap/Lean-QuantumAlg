/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Counting actual oracle events

The weight observes the event kind already present in a run's strict ledger.
It does not grant a query or reinterpret a gate as one.
-/

namespace QuantumAlg.Resource.Event

/-- Count each executed quantum oracle query once, independent of its model-owned coordinate. -/
@[expose] public def oracleWeight {model : ExecutionModel} : Event model → Nat
  | .oracle _ => 1
  | _ => 0

end QuantumAlg.Resource.Event

namespace QuantumAlg.ResourcePool

/-- A point weight that singles out one coordinate equals its exact ledger multiplicity. -/
public theorem weightedCount_eq_count_of_indicator {model : ExecutionModel}
    (weight : Resource.Event model → Nat) (target : Resource.Event model)
    (indicator : ∀ event, weight event = if event = target then 1 else 0)
    (pool : ResourcePool model) :
    weightedCount weight pool = count target pool := by
  induction pool using Multiset.induction_on with
  | empty => simp
  | cons event rest ih =>
      calc
        weightedCount weight (event ::ₘ rest) =
            weight event + weightedCount weight rest := by simp [weightedCount]
        _ = (if event = target then 1 else 0) + count target rest := by
          rw [indicator event, ih]
        _ = count target rest + (if target = event then 1 else 0) := by
          simp [eq_comm, Nat.add_comm]
        _ = count target (event ::ₘ rest) := by simp [count, Multiset.count_cons]

end QuantumAlg.ResourcePool
