/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources

/-!
# Event and duration bounds for declared retry primitives

The first and reused batch bounds include actual recovery and selection.
The pack bounds account for the write to the consumed factor result. Pure
aggregate allowances combine these primitives with one final pack; the
completed finite schedule separately charges every per-batch pack and reset.
All primitive duration bounds allow arbitrary event durations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable {N : Nat}

/-- Optional unpacking and both possible persistent selector writes are reserved per batch. -/
def selectionEventBudget (input : Input N) : ResourcePool (model input) :=
  Optional.eventEnvelope (model input) (modulusBits N)

/-- The real first batch and complete recovery precede the first optional selection. -/
def firstEventBudget (input : Input N) : ResourcePool (model input) :=
  Batch.Recovery.firstEventBudget input + selectionEventBudget input

/-- Every later batch pays for redraw, all quantum resets, complete recovery and selection. -/
def nextEventBudget (input : Input N) : ResourcePool (model input) :=
  Batch.Recovery.nextEventBudget input + selectionEventBudget input

/-- The selected option is packed into the consumed factor cell by one real instruction. -/
def packEvent (input : Input N) : Resource.Event (model input) :=
  .classicalOperation (.nominalEncoding (.packOption (modulusBits N)))

/-- All requested batches execute, with the final selected-result pack charged once. -/
def eventBudget (input : Input N) (laterCount : Nat) : ResourcePool (model input) :=
  firstEventBudget input +
    (ResourcePool.scale laterCount (nextEventBudget input) +
      ResourcePool.singleton (packEvent input))

/-- First sampling and recovery retain their dependencies before the real optional selector. -/
def firstDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  Batch.Recovery.firstDurationBudget input duration +
    ResourcePool.weightedCount duration (selectionEventBudget input)

/-- A later batch retains its reset and sampling dependencies before the same selector. -/
def nextDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  Batch.Recovery.nextDurationBudget input duration +
    ResourcePool.weightedCount duration (selectionEventBudget input)

/-- Actual later batches and the sole final pack follow the first batch in dependency order. -/
def durationBudget (input : Input N) (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  firstDurationBudget input duration +
    (laterCount * nextDurationBudget input duration + duration (packEvent input))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem selection_pool (input : Input N) (path : (select base noQuantum N input).Path) :
    (select base noQuantum N input).resourcePool path ≤ selectionEventBudget input :=
  Optional.into_pool_le (model := model input) (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N) path

private theorem first_pool (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).resourcePool path ≤ firstEventBudget input := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).resourcePool path.2.1 +
        (select base noQuantum N input).resourcePool path.2.2) ≤ _
  rw [zero_add]
  exact add_le_add (Batch.Recovery.declaredRecovery_first_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.2.1)
    (selection_pool base noQuantum N input path.2.2)

theorem next_pool (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).resourcePool path ≤ nextEventBudget input := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).resourcePool path.1 +
      (select base noQuantum N input).resourcePool path.2 ≤ _
  exact add_le_add (Batch.Recovery.declaredRecovery_next_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.1)
    (selection_pool base noQuantum N input path.2)

private theorem selection_depth (input : Input N) (duration : Resource.Event (model input) → Nat)
    (path : (select base noQuantum N input).Path) :
    (select base noQuantum N input).depth duration path ≤
      ResourcePool.weightedCount duration (selectionEventBudget input) :=
  Circuit.depth_le_weightedCount_of_pool_le (select base noQuantum N input) duration
    (selectionEventBudget input) path (selection_pool base noQuantum N input path)

private theorem first_depth (input : Input N) (duration : Resource.Event (model input) → Nat)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).depth duration path ≤ firstDurationBudget input duration := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).depth duration path.2.1 +
        (select base noQuantum N input).depth duration path.2.2) ≤ _
  rw [Nat.zero_add]
  exact Nat.add_le_add (Batch.Recovery.declaredRecovery_first_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.2.1)
    (selection_depth base noQuantum N input duration path.2.2)

theorem next_depth (input : Input N) (duration : Resource.Event (model input) → Nat)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).depth duration path ≤ nextDurationBudget input duration := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).depth duration path.1 +
      (select base noQuantum N input).depth duration path.2 ≤ _
  exact Nat.add_le_add (Batch.Recovery.declaredRecovery_next_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.1)
    (selection_depth base noQuantum N input duration path.2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
