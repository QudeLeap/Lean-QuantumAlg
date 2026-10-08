/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Resources of each actual declared sixteen-sample batch

The first batch draws its real parameter, allocates fixed classical slots,
prepares the original bank once, and performs one fresh sample followed by
fifteen paid reuses. Every later batch redraws in place and pays for sixteen
reuses. The working result and each persistent sample both have their actual
packing charge. Arbitrary native durations preserve the parallel preparation
and member dependencies, followed by each real sequential measurement/write.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable {N : Nat}

/-- One extra paid pack writes the measured exponent cells into their persistent sample slot. -/
def copyEvent (input : Input N) : Resource.Event (model input) :=
  .classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))

/-- The original source draw and complete parameter computation share one fixed model. -/
def sourceEventBudget (input : Input N) : ResourcePool (model input) :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope (model input) N

/-- Source preparation and real per-qubit zero preparation precede the first sample. -/
def setupEventBudget (input : Input N) : ResourcePool (model input) :=
  sourceEventBudget input + preparationEventBudget input

/-- A reused sample pays for its reset, original member and second physical packing. -/
def reusedSampleEventBudget (input : Input N) : ResourcePool (model input) :=
  reuseEventBudget input + ResourcePool.singleton (copyEvent input)

/-- The first batch reserves one fresh sample and fifteen reset samples on the same bank. -/
def firstEventBudget (input : Input N) : ResourcePool (model input) :=
  setupEventBudget input +
    ((memberEventBudget input + ResourcePool.singleton (copyEvent input)) +
      15 • reusedSampleEventBudget input)

/-- A later batch redraws once and reserves sixteen reset samples without another preparation. -/
def nextEventBudget (input : Input N) : ResourcePool (model input) :=
  sourceEventBudget input + 16 • reusedSampleEventBudget input

/-- The classical source allowance is independent of any quantum member dependency. -/
def sourceDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  ResourcePool.weightedCount duration (sourceEventBudget input)

/-- Reset precedes the original member dependency and the persistent-slot packing. -/
def reusedSampleDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  reuseDurationBudget input duration + duration (copyEvent input)

/-- The first allowance preserves parallel bank preparation and every original member depth. -/
def firstDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  (sourceDurationBudget input duration + preparationDuration input duration) +
    ((memberDuration input duration + duration (copyEvent input)) +
      15 * reusedSampleDurationBudget input duration)

/-- A later batch keeps all sixteen actual reset/member/write dependencies in order. -/
def nextDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  sourceDurationBudget input duration + 16 * reusedSampleDurationBudget input duration

private theorem samples_trace {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (width count : Nat)
    (path : (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).Path) :
    (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).eventTrace path =
      [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).eventTrace
        path.1 ++ [] = []
      rw [ih]
      rfl

private theorem slots_trace {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (N : Nat) (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).eventTrace path = [] := by
  change (Native.Batch.Slots.allocateSamples (model := execution)
    ctx (measurementBits N) 16).eventTrace path.1 ++ [] = []
  rw [samples_trace]
  rfl

private theorem samples_depth {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (width count : Nat) (duration : Resource.Event execution → Nat)
    (path : (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).Path) :
    (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).depth duration path =
      0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).depth
        duration path.1 + 0 = 0
      rw [ih, Nat.zero_add]

private theorem slots_depth {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (N : Nat) (duration : Resource.Event execution → Nat)
    (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).depth duration path = 0 := by
  change (Native.Batch.Slots.allocateSamples (model := execution)
    ctx (measurementBits N) 16).depth duration path.1 + 0 = 0
  rw [samples_depth, Nat.zero_add]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private theorem allocate_trace
    (path : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N input).Path) :
    (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N input).eventTrace path = [] := by
  change (MeasurementCells.allocate (model := model input)
    (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N)
    2 (measurementBits N)).eventTrace path.1 ++ [] = []
  rw [MeasurementCells.allocate_eventTrace]
  rfl

private theorem allocate_depth (duration : Resource.Event (model input) → Nat)
    (path : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N input).Path) :
    (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N input).depth duration path = 0 := by
  change (MeasurementCells.allocate (model := model input)
    (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N)
    2 (measurementBits N)).depth duration path.1 + 0 = 0
  rw [MeasurementCells.allocate_depth, Nat.zero_add]

private theorem setup_pool (path : (setup base noQuantum N input).Path) :
    (setup base noQuantum N input).resourcePool path ≤ setupEventBudget input := by
  have slots : (Native.Batch.Slots.allocate (model := model input)
      (sourceContext base N) N).resourcePool path.2.1 = 0 :=
    congrArg ResourcePool.ofList
      (slots_trace (execution := model input) (sourceContext base N) N path.2.1)
  have allocated : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N input).resourcePool path.2.2.2 = 0 :=
    congrArg ResourcePool.ofList (allocate_trace base noQuantum N input path.2.2.2)
  change (ShorStyle.Canonical.Sampler.Retained.circuit (model := model input)
    base N).resourcePool path.1 +
    ((Native.Batch.Slots.allocate (model := model input)
      (sourceContext base N) N).resourcePool path.2.1 +
      ((Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N input).resourcePool path.2.2.1 +
        (Declared.allocate (storageContext base N)
          (storage_empty base noQuantum N) N input).resourcePool path.2.2.2)) ≤ _
  rw [slots, allocated, add_zero, zero_add]
  exact add_le_add
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le
      (model := model input) base N path.1)
    (declaredSample_prepare_resourcePool (storageContext base N)
      (storage_empty base noQuantum N) N input path.2.2.1).le

private theorem copy_pool (index : Fin 16)
    (path : (copy base noQuantum N input index).Path) :
    (copy base noQuantum N input index).resourcePool path =
      ResourcePool.singleton (copyEvent input) := rfl

private theorem reused_pool (index : Fin 16)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).resourcePool path ≤
      reusedSampleEventBudget input := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N)
    N input (parameter base N)).resourcePool path.1 +
      (copy base noQuantum N input index).resourcePool path.2 ≤ _
  exact add_le_add (declaredReuse_resourcePool_le (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N) path.1)
    (copy_pool base noQuantum N input index path.2).le

private theorem first_pool (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).resourcePool path ≤
      (memberEventBudget input + ResourcePool.singleton (copyEvent input)) +
        15 • reusedSampleEventBudget input := by
  have tail := Circuit.forRange_pool_le_sum 15
    (fun index => reusedSample base noQuantum N input index.succ)
    (fun _ => reusedSampleEventBudget input)
    (fun index => reused_pool base noQuantum N input index.succ) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N)
    N input (parameter base N)).resourcePool path.1.1 +
      (copy base noQuantum N input 0).resourcePool path.1.2) +
    (Circuit.forRange 15
      (fun index => reusedSample base noQuantum N input index.succ)).resourcePool path.2 ≤ _
  exact add_le_add
    (add_le_add (declaredSample_body_resourcePool (storageContext base N)
      (storage_empty base noQuantum N) N input (parameter base N) path.1.1).le
      (copy_pool base noQuantum N input 0 path.1.2).le) tail

private theorem redraw_pool (path : (redraw base noQuantum N input).Path) :
    (redraw base noQuantum N input).resourcePool path ≤ sourceEventBudget input := by
  change (ShorStyle.Canonical.Sampler.PackedSample.draw (model := model input)
    N (sourceRef base noQuantum N)).resourcePool path.1 +
    (ShorStyle.Canonical.Sampler.Program.circuit (model := model input) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N)).resourcePool path.2 ≤ _
  exact add_le_add
    (ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_pool (model := model input)
      N (sourceRef base noQuantum N) path.1).le
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_pool_le (model := model input)
      N (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N) path.2)

/-- Every complete first-batch path obeys the original-bank independent event allowance. -/
theorem declaredBatch_resourcePool_le (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).resourcePool path ≤ firstEventBudget input := by
  change (setup base noQuantum N input).resourcePool path.1 +
    (firstBatch base noQuantum N input).resourcePool path.2 ≤ _
  exact add_le_add (setup_pool base noQuantum N input path.1)
    (first_pool base noQuantum N input path.2)

/-- Every later batch pays for the actual redraw and all sixteen original-bank resets. -/
theorem declaredBatch_next_resourcePool_le (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).resourcePool path ≤ nextEventBudget input := by
  have tail := Circuit.forRange_pool_le_sum 16 (reusedSample base noQuantum N input)
    (fun _ => reusedSampleEventBudget input) (reused_pool base noQuantum N input) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change (redraw base noQuantum N input).resourcePool path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N input)).resourcePool path.2 ≤ _
  exact add_le_add (redraw_pool base noQuantum N input path.1) tail

private theorem reused_depth (index : Fin 16) (duration : Resource.Event (model input) → Nat)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).depth duration path ≤
      reusedSampleDurationBudget input duration := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N)
    N input (parameter base N)).depth duration path.1 + duration (copyEvent input) ≤ _
  exact Nat.add_le_add_right (declaredReuse_depth_le (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N) duration path.1) _

private theorem first_depth (duration : Resource.Event (model input) → Nat)
    (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).depth duration path ≤
      (memberDuration input duration + duration (copyEvent input)) +
        15 * reusedSampleDurationBudget input duration := by
  have tail := Circuit.forRange_depth_le_sum 15
    (fun index => reusedSample base noQuantum N input index.succ) duration
    (fun _ => reusedSampleDurationBudget input duration)
    (fun index => reused_depth base noQuantum N input index.succ duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N)
    N input (parameter base N)).depth duration path.1.1 + duration (copyEvent input)) +
    (Circuit.forRange 15
      (fun index => reusedSample base noQuantum N input index.succ)).depth duration path.2 ≤ _
  exact Nat.add_le_add
    (Nat.add_le_add_right (declaredSample_body_depth (storageContext base N)
      (storage_empty base noQuantum N) N input (parameter base N) duration path.1.1).le _) tail

private theorem setup_depth (duration : Resource.Event (model input) → Nat)
    (path : (setup base noQuantum N input).Path) :
    (setup base noQuantum N input).depth duration path ≤
      sourceDurationBudget input duration + preparationDuration input duration := by
  have source := Circuit.depth_le_weightedCount_of_pool_le
    (ShorStyle.Canonical.Sampler.Retained.circuit (model := model input) base N)
    duration (sourceEventBudget input) path.1
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le
      (model := model input) base N path.1)
  change (ShorStyle.Canonical.Sampler.Retained.circuit (model := model input)
    base N).depth duration path.1 +
    ((Native.Batch.Slots.allocate (model := model input)
      (sourceContext base N) N).depth duration path.2.1 +
      ((Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N input).depth duration path.2.2.1 +
        (Declared.allocate (storageContext base N)
          (storage_empty base noQuantum N) N input).depth duration path.2.2.2)) ≤ _
  have slots := slots_depth (execution := model input)
    (sourceContext base N) N duration path.2.1
  have allocated := allocate_depth base noQuantum N input duration path.2.2.2
  have prepared := declaredSample_prepare_depth (storageContext base N)
    (storage_empty base noQuantum N) N input duration path.2.2.1
  have suffix := congrArg₂ Nat.add slots (congrArg₂ Nat.add prepared allocated)
  have normalized : Nat.add 0 (Nat.add (preparationDuration input duration) 0) =
      preparationDuration input duration :=
    (Nat.zero_add (Nat.add (preparationDuration input duration) 0)).trans
      (Nat.add_zero (preparationDuration input duration))
  exact Nat.add_le_add source (suffix.trans normalized).le

/-- The first-batch duration keeps parallel bank preparation and all sixteen member paths. -/
theorem declaredBatch_depth_le (duration : Resource.Event (model input) → Nat)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).depth duration path ≤ firstDurationBudget input duration := by
  change (setup base noQuantum N input).depth duration path.1 +
    (firstBatch base noQuantum N input).depth duration path.2 ≤ _
  exact Nat.add_le_add (setup_depth base noQuantum N input duration path.1)
    (first_depth base noQuantum N input duration path.2)

/-- A later batch retains the actual ordered redraw and sixteen reset/member dependencies. -/
theorem declaredBatch_next_depth_le (duration : Resource.Event (model input) → Nat)
    (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).depth duration path ≤ nextDurationBudget input duration := by
  have head := Circuit.depth_le_weightedCount_of_pool_le (redraw base noQuantum N input)
    duration (sourceEventBudget input) path.1 (redraw_pool base noQuantum N input path.1)
  have tail := Circuit.forRange_depth_le_sum 16 (reusedSample base noQuantum N input) duration
    (fun _ => reusedSampleDurationBudget input duration)
    (fun index => reused_depth base noQuantum N input index duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (redraw base noQuantum N input).depth duration path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N input)).depth duration path.2 ≤ _
  exact Nat.add_le_add head tail

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
