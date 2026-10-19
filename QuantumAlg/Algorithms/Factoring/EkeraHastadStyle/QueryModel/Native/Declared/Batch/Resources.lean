/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Program
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
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
def copyEvent (N : Nat) : Resource.Event (model N) :=
  .classicalOperation (.nominalEncoding (.packFiniteBits (measurementBits N)))

/-- The original source draw and complete parameter computation share one fixed model. -/
def sourceEventBudget (N : Nat) : ResourcePool (model N) :=
  ShorStyle.Canonical.Sampler.Retained.nativeEnvelope (model N) N

/-- Source preparation and real per-qubit zero preparation precede the first sample. -/
def setupEventBudget (N : Nat) : ResourcePool (model N) :=
  sourceEventBudget N + preparationEventBudget N

/-- A reused sample pays for its reset, original member and second physical packing. -/
def reusedSampleEventBudget (N : Nat) : ResourcePool (model N) :=
  reuseEventBudget N + ResourcePool.singleton (copyEvent N)

/-- The first batch reserves one fresh sample and fifteen reset samples on the same bank. -/
def firstEventBudget (N : Nat) : ResourcePool (model N) :=
  setupEventBudget N +
    ((memberEventBudget N + ResourcePool.singleton (copyEvent N)) +
      15 • reusedSampleEventBudget N)

/-- A later batch redraws once and reserves sixteen reset samples without another preparation. -/
def nextEventBudget (N : Nat) : ResourcePool (model N) :=
  sourceEventBudget N + 16 • reusedSampleEventBudget N

/-- The classical source allowance is independent of any quantum member dependency. -/
def sourceDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  ResourcePool.weightedCount duration (sourceEventBudget N)

/-- Reset precedes the original member dependency and the persistent-slot packing. -/
def reusedSampleDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  reuseDurationBudget N duration + duration (copyEvent N)

/-- The first allowance preserves parallel bank preparation and every original member depth. -/
def firstDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  (sourceDurationBudget N duration + preparationDuration N duration) +
    ((memberDuration N duration + duration (copyEvent N)) +
      15 * reusedSampleDurationBudget N duration)

/-- A later batch keeps all sixteen actual reset/member/write dependencies in order. -/
def nextDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  sourceDurationBudget N duration + 16 * reusedSampleDurationBudget N duration

private lemma samples_trace {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
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

private lemma slots_trace {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (N : Nat) (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).eventTrace path = [] := by
  change (Native.Batch.Slots.allocateSamples (model := execution)
    ctx (measurementBits N) 16).eventTrace path.1 ++ [] = []
  rw [samples_trace]
  rfl

private lemma samples_depth {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
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

private lemma slots_depth {execution : ExecutionModel} (ctx : RuntimeCtx execution.kind)
    (N : Nat) (duration : Resource.Event execution → Nat)
    (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).depth duration path = 0 := by
  change (Native.Batch.Slots.allocateSamples (model := execution)
    ctx (measurementBits N) 16).depth duration path.1 + 0 = 0
  rw [samples_depth, Nat.zero_add]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat)

private lemma allocate_trace
    (path : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).Path) :
    (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).eventTrace path = [] := by
  change (MeasurementCells.allocate (model := model N)
    (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N)
    2 (measurementBits N)).eventTrace path.1 ++ [] = []
  rw [MeasurementCells.allocate_eventTrace]
  rfl

private lemma allocate_depth (duration : Resource.Event (model N) → Nat)
    (path : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).Path) :
    (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).depth duration path = 0 := by
  change (MeasurementCells.allocate (model := model N)
    (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N)
    2 (measurementBits N)).depth duration path.1 + 0 = 0
  rw [MeasurementCells.allocate_depth, Nat.zero_add]

private lemma setup_pool (path : (setup base noQuantum N).Path) :
    (setup base noQuantum N).resourcePool path ≤ setupEventBudget N := by
  have slots : (Native.Batch.Slots.allocate (model := model N)
      (sourceContext base N) N).resourcePool path.2.1 = 0 :=
    congrArg ResourcePool.ofList
      (slots_trace (execution := model N) (sourceContext base N) N path.2.1)
  have allocated : (Declared.allocate (storageContext base N)
      (storage_empty base noQuantum N) N).resourcePool path.2.2.2 = 0 :=
    congrArg ResourcePool.ofList (allocate_trace base noQuantum N path.2.2.2)
  change (ShorStyle.Canonical.Sampler.Retained.circuit (model := model N)
    base N).resourcePool path.1 +
    ((Native.Batch.Slots.allocate (model := model N)
      (sourceContext base N) N).resourcePool path.2.1 +
      ((Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).resourcePool path.2.2.1 +
        (Declared.allocate (storageContext base N)
          (storage_empty base noQuantum N) N).resourcePool path.2.2.2)) ≤ _
  rw [slots, allocated, add_zero, zero_add]
  exact add_le_add
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le
      (model := model N) base N path.1)
    (declaredSample_prepare_resourcePool (storageContext base N)
      (storage_empty base noQuantum N) N path.2.2.1).le

private lemma copy_pool (index : Fin 16)
    (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).resourcePool path =
      ResourcePool.singleton (copyEvent N) := rfl

private lemma reused_pool (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).resourcePool path ≤
      reusedSampleEventBudget N := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)).resourcePool path.1 +
      (copy base noQuantum N index).resourcePool path.2 ≤ _
  exact add_le_add (declaredReuse_resourcePool_le (storageContext base N)
    (storage_empty base noQuantum N) N (parameter base N) path.1)
    (copy_pool base noQuantum N index path.2).le

private lemma first_pool (path : (firstBatch base noQuantum N).Path) :
    (firstBatch base noQuantum N).resourcePool path ≤
      (memberEventBudget N + ResourcePool.singleton (copyEvent N)) +
        15 • reusedSampleEventBudget N := by
  have tail := Circuit.forRange_pool_le_sum 15
    (fun index => reusedSample base noQuantum N index.succ)
    (fun _ => reusedSampleEventBudget N)
    (fun index => reused_pool base noQuantum N index.succ) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)).resourcePool path.1.1 +
      (copy base noQuantum N 0).resourcePool path.1.2) +
    (Circuit.forRange 15
      (fun index => reusedSample base noQuantum N index.succ)).resourcePool path.2 ≤ _
  exact add_le_add
    (add_le_add (declaredSample_body_resourcePool (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1.1).le
      (copy_pool base noQuantum N 0 path.1.2).le) tail

private lemma redraw_pool (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).resourcePool path ≤ sourceEventBudget N := by
  change (ShorStyle.Canonical.Sampler.PackedSample.draw (model := model N)
    N (sourceRef base noQuantum N)).resourcePool path.1 +
    (ShorStyle.Canonical.Sampler.Program.circuit (model := model N) N
      (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N)).resourcePool path.2 ≤ _
  exact add_le_add
    (ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_pool (model := model N)
      N (sourceRef base noQuantum N) path.1).le
    (ShorStyle.Canonical.Sampler.Program.samplerProgram_pool_le (model := model N)
      N (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N) path.2)

/-- Every complete first-batch path obeys the original-bank independent event allowance. -/
lemma declaredBatch_resourcePool_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).resourcePool path ≤ firstEventBudget N := by
  change (setup base noQuantum N).resourcePool path.1 +
    (firstBatch base noQuantum N).resourcePool path.2 ≤ _
  exact add_le_add (setup_pool base noQuantum N path.1)
    (first_pool base noQuantum N path.2)

/-- Every later batch pays for the actual redraw and all sixteen original-bank resets. -/
lemma declaredBatch_next_resourcePool_le (path : (nextBatch base noQuantum N).Path) :
    (nextBatch base noQuantum N).resourcePool path ≤ nextEventBudget N := by
  have tail := Circuit.forRange_pool_le_sum 16 (reusedSample base noQuantum N)
    (fun _ => reusedSampleEventBudget N) (reused_pool base noQuantum N) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at tail
  change (redraw base noQuantum N).resourcePool path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N)).resourcePool path.2 ≤ _
  exact add_le_add (redraw_pool base noQuantum N path.1) tail

private lemma reused_depth (index : Fin 16) (duration : Resource.Event (model N) → Nat)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).depth duration path ≤
      reusedSampleDurationBudget N duration := by
  change (reuse (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)).depth duration path.1 + duration (copyEvent N) ≤ _
  exact Nat.add_le_add_right (declaredReuse_depth_le (storageContext base N)
    (storage_empty base noQuantum N) N (parameter base N) duration path.1) _

private lemma first_depth (duration : Resource.Event (model N) → Nat)
    (path : (firstBatch base noQuantum N).Path) :
    (firstBatch base noQuantum N).depth duration path ≤
      (memberDuration N duration + duration (copyEvent N)) +
        15 * reusedSampleDurationBudget N duration := by
  have tail := Circuit.forRange_depth_le_sum 15
    (fun index => reusedSample base noQuantum N index.succ) duration
    (fun _ => reusedSampleDurationBudget N duration)
    (fun index => reused_depth base noQuantum N index.succ duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change ((body (storageContext base N) (storage_empty base noQuantum N)
    N (parameter base N)).depth duration path.1.1 + duration (copyEvent N)) +
    (Circuit.forRange 15
      (fun index => reusedSample base noQuantum N index.succ)).depth duration path.2 ≤ _
  exact Nat.add_le_add
    (Nat.add_le_add_right (declaredSample_body_depth (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) duration path.1.1).le _) tail

private lemma setup_depth (duration : Resource.Event (model N) → Nat)
    (path : (setup base noQuantum N).Path) :
    (setup base noQuantum N).depth duration path ≤
      sourceDurationBudget N duration + preparationDuration N duration := by
  have source := Circuit.depth_le_weightedCount_of_pool_le
    (ShorStyle.Canonical.Sampler.Retained.circuit (model := model N) base N)
    duration (sourceEventBudget N) path.1
    (ShorStyle.Canonical.Sampler.Retained.samplerRetained_pool_le
      (model := model N) base N path.1)
  change (ShorStyle.Canonical.Sampler.Retained.circuit (model := model N)
    base N).depth duration path.1 +
    ((Native.Batch.Slots.allocate (model := model N)
      (sourceContext base N) N).depth duration path.2.1 +
      ((Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).depth duration path.2.2.1 +
        (Declared.allocate (storageContext base N)
          (storage_empty base noQuantum N) N).depth duration path.2.2.2)) ≤ _
  have slots := slots_depth (execution := model N)
    (sourceContext base N) N duration path.2.1
  have allocated := allocate_depth base noQuantum N duration path.2.2.2
  have prepared := declaredSample_prepare_depth (storageContext base N)
    (storage_empty base noQuantum N) N duration path.2.2.1
  have suffix := congrArg₂ Nat.add slots (congrArg₂ Nat.add prepared allocated)
  have normalized : Nat.add 0 (Nat.add (preparationDuration N duration) 0) =
      preparationDuration N duration :=
    (Nat.zero_add (Nat.add (preparationDuration N duration) 0)).trans
      (Nat.add_zero (preparationDuration N duration))
  exact Nat.add_le_add source (suffix.trans normalized).le

/-- The first-batch duration keeps parallel bank preparation and all sixteen member paths. -/
lemma declaredBatch_depth_le (duration : Resource.Event (model N) → Nat)
    (path : (code base noQuantum N).Path) :
    (code base noQuantum N).depth duration path ≤ firstDurationBudget N duration := by
  change (setup base noQuantum N).depth duration path.1 +
    (firstBatch base noQuantum N).depth duration path.2 ≤ _
  exact Nat.add_le_add (setup_depth base noQuantum N duration path.1)
    (first_depth base noQuantum N duration path.2)

/-- A later batch retains the actual ordered redraw and sixteen reset/member dependencies. -/
lemma declaredBatch_next_depth_le (duration : Resource.Event (model N) → Nat)
    (path : (nextBatch base noQuantum N).Path) :
    (nextBatch base noQuantum N).depth duration path ≤ nextDurationBudget N duration := by
  have head := Circuit.depth_le_weightedCount_of_pool_le (redraw base noQuantum N)
    duration (sourceEventBudget N) path.1 (redraw_pool base noQuantum N path.1)
  have tail := Circuit.forRange_depth_le_sum 16 (reusedSample base noQuantum N) duration
    (fun _ => reusedSampleDurationBudget N duration)
    (fun index => reused_depth base noQuantum N index duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (redraw base noQuantum N).depth duration path.1 +
    (Circuit.forRange 16 (reusedSample base noQuantum N)).depth duration path.2 ≤ _
  exact Nat.add_le_add head tail

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
