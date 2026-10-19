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

variable (N : Nat)

/-- Optional unpacking and both possible persistent selector writes are reserved per batch. -/
def selectionEventBudget : ResourcePool (model N) :=
  Optional.eventEnvelope (model N) (modulusBits N)

/-- The real first batch and complete recovery precede the first optional selection. -/
def firstEventBudget : ResourcePool (model N) :=
  Batch.Recovery.firstEventBudget N + selectionEventBudget N

/-- Every later batch pays for redraw, all quantum resets, complete recovery and selection. -/
def nextEventBudget : ResourcePool (model N) :=
  Batch.Recovery.nextEventBudget N + selectionEventBudget N

/-- The selected option is packed into the consumed factor cell by one real instruction. -/
def packEvent : Resource.Event (model N) :=
  .classicalOperation (.nominalEncoding (.packOption (modulusBits N)))

/-- All requested batches execute, with the final selected-result pack charged once. -/
def eventBudget (laterCount : Nat) : ResourcePool (model N) :=
  firstEventBudget N +
    (ResourcePool.scale laterCount (nextEventBudget N) +
      ResourcePool.singleton (packEvent N))

/-- First sampling and recovery retain their dependencies before the real optional selector. -/
def firstDurationBudget
    (duration : Resource.Event (model N) → Nat) : Nat :=
  Batch.Recovery.firstDurationBudget N duration +
    ResourcePool.weightedCount duration (selectionEventBudget N)

/-- A later batch retains its reset and sampling dependencies before the same selector. -/
def nextDurationBudget
    (duration : Resource.Event (model N) → Nat) : Nat :=
  Batch.Recovery.nextDurationBudget N duration +
    ResourcePool.weightedCount duration (selectionEventBudget N)

/-- Actual later batches and the sole final pack follow the first batch in dependency order. -/
def durationBudget (laterCount : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  firstDurationBudget N duration +
    (laterCount * nextDurationBudget N duration + duration (packEvent N))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private lemma selection_pool (path : (select base noQuantum N).Path) :
    (select base noQuantum N).resourcePool path ≤ selectionEventBudget N :=
  Optional.into_pool_le (model := model N) (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N) path

private lemma first_pool (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).resourcePool path ≤ firstEventBudget N := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).resourcePool path.2.1 +
        (select base noQuantum N).resourcePool path.2.2) ≤ _
  rw [zero_add]
  exact add_le_add (Batch.Recovery.declaredRecovery_first_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.2.1)
    (selection_pool base noQuantum N path.2.2)

lemma next_pool (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).resourcePool path ≤ nextEventBudget N := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).resourcePool path.1 +
      (select base noQuantum N).resourcePool path.2 ≤ _
  exact add_le_add (Batch.Recovery.declaredRecovery_next_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.1)
    (selection_pool base noQuantum N path.2)

private lemma selection_depth (duration : Resource.Event (model N) → Nat)
    (path : (select base noQuantum N).Path) :
    (select base noQuantum N).depth duration path ≤
      ResourcePool.weightedCount duration (selectionEventBudget N) :=
  Circuit.depth_le_weightedCount_of_pool_le (select base noQuantum N) duration
    (selectionEventBudget N) path (selection_pool base noQuantum N path)

private lemma first_depth (input : Input N) (duration : Resource.Event (model N) → Nat)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).depth duration path ≤ firstDurationBudget N duration := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).depth duration path.2.1 +
        (select base noQuantum N).depth duration path.2.2) ≤ _
  rw [Nat.zero_add]
  exact Nat.add_le_add (Batch.Recovery.declaredRecovery_first_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.2.1)
    (selection_depth base noQuantum N duration path.2.2)

lemma next_depth (input : Input N) (duration : Resource.Event (model N) → Nat)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).depth duration path ≤ nextDurationBudget N duration := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).depth duration path.1 +
      (select base noQuantum N).depth duration path.2 ≤ _
  exact Nat.add_le_add (Batch.Recovery.declaredRecovery_next_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.1)
    (selection_depth base noQuantum N duration path.2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
