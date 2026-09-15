/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery.Resources

/-!
# Actual positive retry event and duration allowances

One real first batch is followed by every requested later batch on the same
bank. Each batch includes recovery and optional first-success selection,
even after an earlier acceptance. The sole final pack overwrites the consumed
factor result. Actual retention contributes storage but no native event.
Arbitrary durations keep the original sampling tensor critical paths and
charge all reset, classical recovery, selection and final-pack work.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- The actual optional decoder and both possible first-success writes are paid per batch. -/
def selectionEventBudget (N : Nat) : ResourcePool .quantum :=
  Optional.eventEnvelope .quantum (modulusBits N)

/-- The original first batch and its recovery precede the first optional selection. -/
def firstEventBudget (N : Nat) : ResourcePool .quantum :=
  Batch.Recovery.firstEventBudget N + selectionEventBudget N

/-- Every later batch pays for the full redraw, recovery and optional selection. -/
def nextEventBudget (N : Nat) : ResourcePool .quantum :=
  Batch.Recovery.nextEventBudget N + selectionEventBudget N

/-- The final actual pack writes the selected option into the consumed factor cell. -/
def packEvent (N : Nat) : Resource.Event .quantum :=
  .classicalOperation (.nominalEncoding (.packOption (modulusBits N)))

/-- The actual ordered retry is charged once per real batch and once for its final pack. -/
def eventBudget (N laterCount : Nat) : ResourcePool .quantum :=
  firstEventBudget N +
    (ResourcePool.scale laterCount (nextEventBudget N) + ResourcePool.singleton (packEvent N))

/-- Actual first sampling dependencies precede the original classical recovery and selection. -/
def firstDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  Batch.Recovery.firstDurationBudget N duration +
    ResourcePool.weightedCount duration (selectionEventBudget N)

/-- Later sampling keeps its original reset and tensor dependencies before the same selector. -/
def nextDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  Batch.Recovery.nextDurationBudget N duration +
    ResourcePool.weightedCount duration (selectionEventBudget N)

/-- All requested later batches and the final pack contribute their actual dependency order. -/
def durationBudget (N laterCount : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  firstDurationBudget N duration +
    (laterCount * nextDurationBudget N duration + duration (packEvent N))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem selection_pool (path : (select base noQuantum N).Path) :
    (select base noQuantum N).resourcePool path ≤ selectionEventBudget N :=
  Optional.into_pool_le (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N) path

private theorem first_pool (input : Input N) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).resourcePool path ≤ firstEventBudget N := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).resourcePool path.2.1 +
        (select base noQuantum N).resourcePool path.2.2) ≤ _
  rw [zero_add]
  exact add_le_add (Batch.Recovery.nativeOracle_recovery_first_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.2.1)
    (selection_pool base noQuantum N path.2.2)

private theorem next_pool (input : Input N) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).resourcePool path ≤ nextEventBudget N := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).resourcePool path.1 +
      (select base noQuantum N).resourcePool path.2 ≤ _
  exact add_le_add (Batch.Recovery.nativeOracle_recovery_next_resourcePool_le
    (callerContext base N) (caller_empty base noQuantum N) N input path.1)
    (selection_pool base noQuantum N path.2)

/-- The complete actual positive retry meets the independent native allowance on every path. -/
theorem nativeOracle_retry_resourcePool_le (input : Input N) (laterCount : Nat)
    (path : (code base noQuantum N input laterCount).Path) :
    (code base noQuantum N input laterCount).resourcePool path ≤ eventBudget N laterCount := by
  have tail := Circuit.forRange_pool_le laterCount (fun _ => next base noQuantum N input)
    (nextEventBudget N) (fun _ => next_pool base noQuantum N input) path.2.1
  change (first base noQuantum N input).resourcePool path.1 +
    ((Circuit.forRange laterCount (fun _ => next base noQuantum N input)).resourcePool path.2.1 +
      ResourcePool.singleton (packEvent N)) ≤ _
  exact add_le_add (first_pool base noQuantum N input path.1) (add_le_add tail le_rfl)

private theorem selection_depth (duration : Resource.Event .quantum → Nat)
    (path : (select base noQuantum N).Path) :
    (select base noQuantum N).depth duration path ≤
      ResourcePool.weightedCount duration (selectionEventBudget N) :=
  Circuit.depth_le_weightedCount_of_pool_le (select base noQuantum N) duration
    (selectionEventBudget N) path (selection_pool base noQuantum N path)

private theorem first_depth (input : Input N) (duration : Resource.Event .quantum → Nat)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).depth duration path ≤ firstDurationBudget N duration := by
  change 0 +
    ((Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input).depth duration path.2.1 +
        (select base noQuantum N).depth duration path.2.2) ≤ _
  rw [Nat.zero_add]
  exact Nat.add_le_add (Batch.Recovery.nativeOracle_recovery_first_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.2.1)
    (selection_depth base noQuantum N duration path.2.2)

private theorem next_depth (input : Input N) (duration : Resource.Event .quantum → Nat)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).depth duration path ≤ nextDurationBudget N duration := by
  change (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input).depth duration path.1 +
      (select base noQuantum N).depth duration path.2 ≤ _
  exact Nat.add_le_add (Batch.Recovery.nativeOracle_recovery_next_depth_le
    (callerContext base N) (caller_empty base noQuantum N) N input duration path.1)
    (selection_depth base noQuantum N duration path.2)

/-- Arbitrary durations retain the real sampling critical paths throughout the actual retry. -/
theorem nativeOracle_retry_depth_le (input : Input N) (laterCount : Nat)
    (duration : Resource.Event .quantum → Nat)
    (path : (code base noQuantum N input laterCount).Path) :
    (code base noQuantum N input laterCount).depth duration path ≤
      durationBudget N laterCount duration := by
  have tail := Circuit.forRange_depth_le_sum laterCount
    (fun _ => next base noQuantum N input) duration (fun _ => nextDurationBudget N duration)
    (fun _ => next_depth base noQuantum N input duration) path.2.1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (first base noQuantum N input).depth duration path.1 +
    ((Circuit.forRange laterCount (fun _ => next base noQuantum N input)).depth duration path.2.1 +
      duration (packEvent N)) ≤ _
  exact Nat.add_le_add (first_depth base noQuantum N input duration path.1)
    (Nat.add_le_add_right tail _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
