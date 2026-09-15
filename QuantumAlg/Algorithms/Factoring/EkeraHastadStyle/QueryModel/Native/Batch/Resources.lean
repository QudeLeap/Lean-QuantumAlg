/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Actual event and duration allowances for the fixed original oracle batch

The first batch draws and computes its real parameter, prepares one bank,
runs one original member and fifteen paid reuses. A later batch redraws in
the same cells and performs sixteen paid reuses. Every member writes its
persistent slot with the additional actual finite-bit pack. The working
pack, terminal Zs and reset measurements/corrections remain charged.

Arbitrary-duration bounds keep each member's original tensor critical path.
Only the classical source preparation uses its weighted native allowance.
These budgets do not assert the old oracle-only depth contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

/-- The extra actual pack writes one measured sample into its persistent slot. -/
def copyEvent (N : Nat) : Resource.Event .quantum :=
  .classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))

/-- Actual redraw plus all native instructions of the original stored-parameter computation. -/
def sourceEventBudget (N : Nat) : ResourcePool .quantum :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N

/-- The only bank preparation occurs after the real source draw and fixed slot allocations. -/
def setupEventBudget (N : Nat) : ResourcePool .quantum :=
  sourceEventBudget N + ResourcePool.singleton (preparation N).event

/-- A subsequent member pays for reset, the original member and its persistent sample pack. -/
def reusedSampleEventBudget (N : Nat) : ResourcePool .quantum :=
  reuseEventBudget N + ResourcePool.singleton (copyEvent N)

/-- First preparation is followed by one fresh member and fifteen actual reset members. -/
def firstEventBudget (N : Nat) : ResourcePool .quantum :=
  setupEventBudget N +
    ((memberEventBudget N + ResourcePool.singleton (copyEvent N)) +
      15 • reusedSampleEventBudget N)

/-- A later complete batch redraws once and performs sixteen actual reset members. -/
def nextEventBudget (N : Nat) : ResourcePool .quantum :=
  sourceEventBudget N + 16 • reusedSampleEventBudget N

/-- The source allowance is weighted independently of any quantum member's critical path. -/
def sourceDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  ResourcePool.weightedCount duration (sourceEventBudget N)

/-- The original member critical path follows the actual reset and precedes its extra pack. -/
def reusedSampleDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  reuseDurationBudget N duration + duration (copyEvent N)

/-- The first batch charges one actual preparation and every original tensor member depth. -/
def firstDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  (sourceDurationBudget N duration + duration (preparation N).event) +
    ((memberDuration N duration + duration (copyEvent N)) +
      15 * reusedSampleDurationBudget N duration)

/-- A later batch charges the real source work and every reset/member/pack dependency. -/
def nextDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  sourceDurationBudget N duration + 16 * reusedSampleDurationBudget N duration

private theorem samples_trace {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width count : Nat) (path : (Slots.allocateSamples ctx width count).Path) :
    (Slots.allocateSamples ctx width count).eventTrace path = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (Slots.allocateSamples ctx width count).eventTrace path.1 ++ [] = []
      rw [ih]
      rfl

private theorem slots_trace {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat)
    (path : (Slots.allocate ctx N).Path) : (Slots.allocate ctx N).eventTrace path = [] := by
  change (Slots.allocateSamples ctx (measurementBits N) 16).eventTrace path.1 ++ [] = []
  rw [samples_trace]
  rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem native_allocate_trace
    (path : (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N).Path) :
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N).eventTrace path =
      [] := by
  change (MeasurementCells.allocate
    (bankContext (storageContext base N) (storage_empty base noQuantum N) N)
    2 (measurementBits N)).eventTrace path.1 ++ [] = []
  rw [MeasurementCells.allocate_eventTrace]
  rfl

private theorem setup_pool (path : (setup base noQuantum N).Path) :
    (setup base noQuantum N).resourcePool path ≤ setupEventBudget N := by
  have slots : (Slots.allocate (sourceContext base N) N).resourcePool path.2.1 = 0 :=
    congrArg ResourcePool.ofList (slots_trace (sourceContext base N) N path.2.1)
  have allocated : (Native.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).resourcePool path.2.2.2 = 0 :=
    congrArg ResourcePool.ofList (native_allocate_trace base noQuantum N path.2.2.2)
  change (ShorStyle.Canonical.Sampler.Retained.circuit base N).resourcePool path.1 +
    ((Slots.allocate (sourceContext base N) N).resourcePool path.2.1 +
      (ResourcePool.singleton (preparation N).event +
        (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N).resourcePool
          path.2.2.2)) ≤ _
  rw [slots, allocated, add_zero, zero_add]
  exact add_le_add (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le base N path.1)
    (le_refl _)

private theorem copy_pool (index : Fin 16) (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).resourcePool path = ResourcePool.singleton (copyEvent N) := rfl

private theorem reused_pool (input : Input N) (index : Fin 16)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).resourcePool path ≤
      reusedSampleEventBudget N := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).resourcePool path.1 + (copy base noQuantum N index).resourcePool path.2 ≤ _
  exact add_le_add (nativeOracle_reuse_resourcePool_le (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N) path.1)
    (copy_pool base noQuantum N index path.2).le

private theorem first_pool (input : Input N) (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).resourcePool path ≤
      (memberEventBudget N + ResourcePool.singleton (copyEvent N)) +
        15 • reusedSampleEventBudget N := by
  have tail := Circuit.forRange_pool_le_sum 15
    (fun index => reusedSample base noQuantum N input index.succ)
    (fun _ => reusedSampleEventBudget N)
    (fun index => reused_pool base noQuantum N input index.succ) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).resourcePool path.1.1 + (copy base noQuantum N 0).resourcePool path.1.2) +
      (Circuit.forRange 15
        (fun index => reusedSample base noQuantum N input index.succ)).resourcePool
        path.2 ≤ _
  exact add_le_add
    (add_le_add (body_pool (storageContext base N) (storage_empty base noQuantum N) N
      input (parameter base N) path.1.1).le (copy_pool base noQuantum N 0 path.1.2).le) tail

private theorem redraw_pool (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).resourcePool path ≤ sourceEventBudget N := by
  change (ShorStyle.Canonical.Sampler.PackedSample.draw N
    (sourceRef base noQuantum N)).resourcePool path.1 +
      (ShorStyle.Canonical.Sampler.Program.circuit N
        (.storage (sourceRef base noQuantum N).toCStorageRef)
        (parameterRef base noQuantum N)).resourcePool path.2 ≤ _
  exact add_le_add
    (ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_pool N
      (sourceRef base noQuantum N) path.1).le
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_pool_le N
      (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N) path.2)

/-- The complete actual first batch obeys the independent source/preparation/member allowance. -/
theorem nativeOracle_batch_resourcePool_le (input : Input N)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).resourcePool path ≤ firstEventBudget N := by
  change (setup base noQuantum N).resourcePool path.1 +
    (firstBatch base noQuantum N input).resourcePool path.2 ≤ _
  exact add_le_add (setup_pool base noQuantum N path.1) (first_pool base noQuantum N input path.2)

/-- The next actual batch charges its real redraw and all sixteen paid bank reuses. -/
theorem nativeOracle_nextBatch_resourcePool_le (input : Input N)
    (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).resourcePool path ≤ nextEventBudget N := by
  have tail := Circuit.forRange_pool_le_sum 16 (reusedSample base noQuantum N input)
    (fun _ => reusedSampleEventBudget N) (reused_pool base noQuantum N input) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change (redraw base noQuantum N).resourcePool path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N input)).resourcePool path.2 ≤ _
  exact add_le_add (redraw_pool base noQuantum N path.1) tail

private theorem reused_depth (input : Input N) (index : Fin 16)
    (duration : Resource.Event .quantum → Nat)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).depth duration path ≤
      reusedSampleDurationBudget N duration := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).depth duration path.1 + duration (copyEvent N) ≤ _
  exact Nat.add_le_add_right (nativeOracle_reuse_depth_le (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N) duration path.1) _

private theorem first_depth (input : Input N) (duration : Resource.Event .quantum → Nat)
    (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).depth duration path ≤
      (memberDuration N duration + duration (copyEvent N)) +
        15 * reusedSampleDurationBudget N duration := by
  have tail := Circuit.forRange_depth_le_sum 15
    (fun index => reusedSample base noQuantum N input index.succ) duration
    (fun _ => reusedSampleDurationBudget N duration)
    (fun index => reused_depth base noQuantum N input index.succ duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N) N input
    (parameter base N)).depth duration path.1.1 + duration (copyEvent N)) +
      (Circuit.forRange 15 (fun index => reusedSample base noQuantum N input index.succ)).depth
        duration path.2 ≤ _
  exact Nat.add_le_add
    (Nat.add_le_add_right (body_depth (storageContext base N)
      (storage_empty base noQuantum N) N input (parameter base N) duration path.1.1).le _) tail

/-- Arbitrary durations preserve the original member critical paths in the complete first batch. -/
theorem nativeOracle_batch_depth_le (input : Input N) (duration : Resource.Event .quantum → Nat)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).depth duration path ≤ firstDurationBudget N duration := by
  have setupBound := Circuit.depth_le_weightedCount_of_pool_le (setup base noQuantum N)
    duration (setupEventBudget N) path.1 (setup_pool base noQuantum N path.1)
  simp only [setupEventBudget, ResourcePool.weightedCount_add,
    ResourcePool.weightedCount_singleton, Nat.one_mul] at setupBound
  change (setup base noQuantum N).depth duration path.1 +
    (firstBatch base noQuantum N input).depth duration path.2 ≤ _
  exact Nat.add_le_add setupBound (first_depth base noQuantum N input duration path.2)

/-- Arbitrary durations charge the later redraw and every original reset/member dependency. -/
theorem nativeOracle_nextBatch_depth_le (input : Input N)
    (duration : Resource.Event .quantum → Nat) (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).depth duration path ≤ nextDurationBudget N duration := by
  have head := Circuit.depth_le_weightedCount_of_pool_le (redraw base noQuantum N) duration
    (sourceEventBudget N) path.1 (redraw_pool base noQuantum N path.1)
  have tail := Circuit.forRange_depth_le_sum 16 (reusedSample base noQuantum N input) duration
    (fun _ => reusedSampleDurationBudget N duration)
    (fun index => reused_depth base noQuantum N input index duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (redraw base noQuantum N).depth duration path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N input)).depth duration path.2 ≤ _
  exact Nat.add_le_add head tail

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
