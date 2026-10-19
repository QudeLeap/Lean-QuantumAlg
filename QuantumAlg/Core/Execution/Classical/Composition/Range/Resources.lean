/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range
import Mathlib.Algebra.BigOperators.Fin

/-!
# Individual resource allowances for actual indexed sequences

Each existing indexed body retains its own independent native-event and
duration allowance. The full actual sequence adds those allowances in its
original order, without replacing distinct stages by a shared maximum.
Exact serial event-duration equations also compose through the same paths.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
variable {allowAllocation : Bool}

/-- A native event that occurs the same number of times in every component
occurs exactly that number times the length of the actual indexed sequence. -/
lemma forRange_event_count (event : Resource.Event model) (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation) (amount : Nat)
    (equations : ∀ index path,
      ResourcePool.count event ((body index).resourcePool path) = amount)
    (path : (forRange count body).Path) :
    ResourcePool.count event ((forRange count body).resourcePool path) =
      count * amount := by
  induction count with
  | zero =>
      change ResourcePool.count event (0 : ResourcePool model) = 0 * amount
      simp
  | succ count ih =>
      change ResourcePool.count event
        ((body 0).resourcePool path.1 +
          (forRange count (fun index => body index.succ)).resourcePool path.2) = _
      erw [ResourcePool.count_add, equations, ih _ (fun index => equations index.succ)]
      ring

/-- The actual sequence adds every stage's own independent native-event allowance. -/
lemma forRange_pool_le_sum (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (budgets : Fin count → ResourcePool model)
    (bounds : ∀ index path, (body index).resourcePool path ≤ budgets index)
    (path : (forRange count body).Path) :
    (forRange count body).resourcePool path ≤ ∑ index, budgets index := by
  induction count with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact le_rfl
  | succ count ih =>
      change ResourcePool.ofList ((body 0).eventTrace path.1 ++
        (forRange count (fun index => body index.succ)).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append, Fin.sum_univ_succ]
      exact add_le_add (bounds 0 path.1)
        (ih _ (fun index => budgets index.succ) (fun index => bounds index.succ) path.2)

/-- Arbitrary event durations add the distinct original dependency allowance of every stage. -/
lemma forRange_depth_le_sum (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (duration : Resource.Event model → Nat) (budgets : Fin count → Nat)
    (bounds : ∀ index path, (body index).depth duration path ≤ budgets index)
    (path : (forRange count body).Path) :
    (forRange count body).depth duration path ≤ ∑ index, budgets index := by
  induction count with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact Nat.le_refl 0
  | succ count ih =>
      change (body 0).depth duration path.1 +
        (forRange count (fun index => body index.succ)).depth duration path.2 ≤ _
      rw [Fin.sum_univ_succ]
      exact Nat.add_le_add (bounds 0 path.1)
        (ih _ (fun index => budgets index.succ) (fun index => bounds index.succ) path.2)

/-- Actual serial event-duration equations compose on the same complete indexed-sequence path. -/
lemma forRange_duration_eventTrace (count : Nat)
    (body : Fin count → Circuit model ctx ctx allowAllocation)
    (duration : Resource.Event model → Nat)
    (equations : ∀ index path, (body index).depth duration path =
      (((body index).eventTrace path).map duration).sum)
    (path : (forRange count body).Path) :
    (forRange count body).depth duration path =
      (((forRange count body).eventTrace path).map duration).sum := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (body 0).depth duration path.1 +
        (forRange count (fun index => body index.succ)).depth duration path.2 =
          (((body 0).eventTrace path.1 ++
            (forRange count (fun index => body index.succ)).eventTrace path.2).map duration).sum
      rw [List.map_append, List.sum_append]
      exact congrArg₂ (· + ·) (equations 0 path.1)
        (ih _ (fun index => equations index.succ) path.2)

end

end QuantumAlg.Circuit
