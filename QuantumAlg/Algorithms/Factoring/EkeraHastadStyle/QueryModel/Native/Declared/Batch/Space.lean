/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Program
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Actual live storage of the declared original-bank batch

The actual source cells, sixteen sample slots, factor result, measurement
cells and working packed result remain in one context with the original bank.
Redraw uses the original classical sampler scratch; a quantum reset uses
one finite classical scratch cell per bank wire. These scopes run sequentially, so their
uniform allowance is a maximum. Neither scratch nor the fixed slots are
multiplied by the number of samples or later batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

/-- Every retained result representation and the sole original quantum bank are counted. -/
def retainedSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (measurementBits N)) +
    measurementBits N • SpacePool.ofShape (.finite 2) +
      SpacePool.ofQuantumLayout (Native.layout N) +
        (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
          16 • SpacePool.ofShape (.bits (measurementBits N)) +
            ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))

/-- Sequential source computation and reset share the maximum of their actual scratch budgets. -/
def scratchSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.max (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (resetSpace N)

/-- A uniform first/later-batch allowance includes the fixed storage and live scratch maximum. -/
def additionalSpace (N : Nat) : SpacePool .quantum := retainedSpace N + scratchSpace N

private lemma samples_resident (ctx : RuntimeCtx .quantum) (width count : Nat) :
    (Native.Batch.Slots.samples ctx width count).residentSpace =
      count • SpacePool.ofShape (.bits width) + ctx.residentSpace := by
  induction count with
  | zero => simp only [Native.Batch.Slots.samples, zero_nsmul, zero_add]
  | succ count ih =>
      rw [Native.Batch.Slots.samples, RuntimeCtx.residentSpace_addRetained, ih, succ_nsmul]
      ac_rfl

private lemma slots_resident (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Native.Batch.Slots.context ctx N).residentSpace =
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + ctx.residentSpace := by
  rw [Native.Batch.Slots.context, RuntimeCtx.residentSpace_addRetained, samples_resident, add_assoc]

private lemma samples_peak_resident {execution : ExecutionModel}
    (ctx : RuntimeCtx execution.kind) (width count : Nat)
    (path : (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).Path) :
    (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).peakResidentSpace
        path ≤
      (Native.Batch.Slots.samples ctx width count).residentSpace := by
  induction count with
  | zero =>
      intro axis
      change max (ctx.residentSpace axis) 0 ≤ ctx.residentSpace axis
      omega
  | succ count ih =>
      refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (ih path.1).trans ?_
        change (Native.Batch.Slots.samples ctx width count).residentSpace ≤
          SpacePool.ofShape (.bits width) +
            (Native.Batch.Slots.samples ctx width count).residentSpace
        exact fun axis => Nat.le_add_left _ _
      · intro axis
        change max ((Native.Batch.Slots.samples ctx width count).residentSpace axis)
          (max ((Native.Batch.Slots.samples ctx width (count + 1)).residentSpace axis) 0) ≤
            (Native.Batch.Slots.samples ctx width (count + 1)).residentSpace axis
        have growing : (Native.Batch.Slots.samples ctx width count).residentSpace axis ≤
            (Native.Batch.Slots.samples ctx width (count + 1)).residentSpace axis :=
          Nat.le_add_left _ _
        omega

private lemma slots_peak_resident {execution : ExecutionModel}
    (ctx : RuntimeCtx execution.kind) (N : Nat)
    (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).peakResidentSpace path ≤
      (Native.Batch.Slots.context ctx N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (samples_peak_resident (execution := execution)
      ctx (measurementBits N) 16 path.1).trans ?_
    exact fun axis => Nat.le_add_left _ _
  · intro axis
    change max ((Native.Batch.Slots.samples ctx (measurementBits N) 16).residentSpace axis)
      (max ((Native.Batch.Slots.context ctx N).residentSpace axis) 0) ≤
        (Native.Batch.Slots.context ctx N).residentSpace axis
    have growing : (Native.Batch.Slots.samples ctx (measurementBits N) 16).residentSpace axis ≤
        (Native.Batch.Slots.context ctx N).residentSpace axis := Nat.le_add_left _ _
    omega

private lemma samples_auxiliary (ctx : RuntimeCtx .quantum) (width count : Nat) :
    (Native.Batch.Slots.samples ctx width count).auxiliarySpace =
      count • SpacePool.ofShape (.bits width) + ctx.auxiliarySpace := by
  induction count with
  | zero => simp only [Native.Batch.Slots.samples, zero_nsmul, zero_add]
  | succ count ih =>
      rw [Native.Batch.Slots.samples, RuntimeCtx.auxiliarySpace_addRetained, ih, succ_nsmul]
      ac_rfl

private lemma slots_auxiliary (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Native.Batch.Slots.context ctx N).auxiliarySpace =
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + ctx.auxiliarySpace := by
  rw [Native.Batch.Slots.context, RuntimeCtx.auxiliarySpace_addRetained,
    samples_auxiliary, add_assoc]

private lemma samples_peak_auxiliary {execution : ExecutionModel}
    (ctx : RuntimeCtx execution.kind) (width count : Nat)
    (path : (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).Path) :
    (Native.Batch.Slots.allocateSamples (model := execution) ctx width count).peakAuxiliarySpace
        path ≤
      (Native.Batch.Slots.samples ctx width count).auxiliarySpace := by
  induction count with
  | zero =>
      intro axis
      change max (ctx.auxiliarySpace axis) 0 ≤ ctx.auxiliarySpace axis
      omega
  | succ count ih =>
      refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (ih path.1).trans ?_
        change (Native.Batch.Slots.samples ctx width count).auxiliarySpace ≤
          SpacePool.ofShape (.bits width) +
            (Native.Batch.Slots.samples ctx width count).auxiliarySpace
        exact fun axis => Nat.le_add_left _ _
      · intro axis
        change max ((Native.Batch.Slots.samples ctx width count).auxiliarySpace axis)
          (max ((Native.Batch.Slots.samples ctx width (count + 1)).auxiliarySpace axis) 0) ≤
            (Native.Batch.Slots.samples ctx width (count + 1)).auxiliarySpace axis
        have growing : (Native.Batch.Slots.samples ctx width count).auxiliarySpace axis ≤
            (Native.Batch.Slots.samples ctx width (count + 1)).auxiliarySpace axis :=
          Nat.le_add_left _ _
        omega

private lemma slots_peak_auxiliary {execution : ExecutionModel}
    (ctx : RuntimeCtx execution.kind) (N : Nat)
    (path : (Native.Batch.Slots.allocate (model := execution) ctx N).Path) :
    (Native.Batch.Slots.allocate (model := execution) ctx N).peakAuxiliarySpace path ≤
      (Native.Batch.Slots.context ctx N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (samples_peak_auxiliary (execution := execution)
      ctx (measurementBits N) 16 path.1).trans ?_
    exact fun axis => Nat.le_add_left _ _
  · intro axis
    change max ((Native.Batch.Slots.samples ctx (measurementBits N) 16).auxiliarySpace axis)
      (max ((Native.Batch.Slots.context ctx N).auxiliarySpace axis) 0) ≤
        (Native.Batch.Slots.context ctx N).auxiliarySpace axis
    have growing : (Native.Batch.Slots.samples ctx (measurementBits N) 16).auxiliarySpace axis ≤
        (Native.Batch.Slots.context ctx N).auxiliarySpace axis := Nat.le_add_left _ _
    omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The fixed batch context counts its exact resident capacity beside the original caller. -/
lemma declaredBatch_context_residentSpace :
    (context base noQuantum N).residentSpace = retainedSpace N + base.residentSpace := by
  change (Native.context (storageContext base N)
    (storage_empty base noQuantum N) N).residentSpace = _
  rw [declaredSample_context_residentSpace, storageContext, slots_resident, sourceContext,
    ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident]
  unfold retainedSpace
  ac_rfl

private lemma storage_resident_le :
    (storageContext base N).residentSpace ≤ (context base noQuantum N).residentSpace := by
  change (storageContext base N).residentSpace ≤
    (Native.context (storageContext base N) (storage_empty base noQuantum N) N).residentSpace
  rw [declaredSample_context_residentSpace]
  exact fun axis => Nat.le_add_left _ _

private lemma source_resident_le :
    (sourceContext base N).residentSpace ≤ (context base noQuantum N).residentSpace := by
  refine (show (sourceContext base N).residentSpace ≤
    (storageContext base N).residentSpace from ?_).trans
    (storage_resident_le base noQuantum N)
  rw [storageContext, slots_resident]
  exact fun axis => Nat.le_add_left _ _

private lemma copy_resident (index : Fin 16)
    (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).peakResidentSpace path =
      (context base noQuantum N).residentSpace := by
  funext axis
  exact Nat.max_zero _

/-- A reused sample has one live reset bit per wire beyond the complete fixed batch context. -/
lemma declaredBatch_reusedSample_peakResidentSpace (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).peakResidentSpace path =
      resetSpace N + (context base noQuantum N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).trans ?_
  refine (congrArg₂ SpacePool.max
    (declaredReuse_peakResidentSpace (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1)
    (copy_resident base noQuantum N index path.2)).trans ?_
  exact SpacePool.max_eq_left (fun axis => Nat.le_add_left _ _)

private lemma reused_resident (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  refine (declaredBatch_reusedSample_peakResidentSpace
    base noQuantum N index path).le.trans ?_
  intro axis
  have scratch := SpacePool.le_max_right
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (resetSpace N) axis
  change resetSpace N axis +
    (context base noQuantum N).residentSpace axis ≤
      (context base noQuantum N).residentSpace axis + scratchSpace N axis
  change _ ≤ scratchSpace N axis at scratch
  omega

private lemma first_resident
    (path : (firstBatch base noQuantum N).Path) :
    (firstBatch base noQuantum N).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  have tail := Circuit.forRange_resident_le 15
    (fun index => reusedSample base noQuantum N index.succ)
    ((context base noQuantum N).residentSpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _)
    (fun index => reused_resident base noQuantum N index.succ) path.2
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ tail)
  refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
  · exact (declaredSample_body_peakResidentSpace (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1.1).le.trans
        (fun axis => Nat.le_add_right _ _)
  · exact (copy_resident base noQuantum N 0 path.1.2).le.trans
      (fun axis => Nat.le_add_right _ _)

private lemma setup_resident
    (path : (setup base noQuantum N).Path)
    (bodyPath : (body (storageContext base N) (storage_empty base noQuantum N) N
      (parameter base N)).Path) :
    (setup base noQuantum N).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  have source := ShorStyle.Canonical.Sampler.Retained.samplerRetained_resident_le
    (model := model N) base N path.1
  have sourceBudget := ShorStyle.Canonical.Sampler.Retained.resident_budget base N
  have sourceLimit :
      (ShorStyle.Canonical.Sampler.Retained.circuit (model := model N)
        base N).peakResidentSpace path.1 ≤
          (context base noQuantum N).residentSpace + scratchSpace N :=
    source.trans (sourceBudget.symm.trans_le
      (add_le_add (source_resident_le base noQuantum N) (SpacePool.le_max_left _ _)))
  have storage := (slots_peak_resident (execution := model N)
    (sourceContext base N) N path.2.1).trans (storage_resident_le base noQuantum N)
  have core := declaredSample_peakResidentSpace (storageContext base N)
    (storage_empty base noQuantum N) N (parameter base N)
    (path.2.2.1, (path.2.2.2, bodyPath))
  simp only [Declared.code, Circuit.peakResidentSpace_seq] at core
  have prepared :
      (Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).peakResidentSpace path.2.2.1 ≤
          (context base noQuantum N).residentSpace :=
    (SpacePool.le_max_left _ _).trans_eq core
  have allocated :
      (Declared.allocate (storageContext base N)
        (storage_empty base noQuantum N) N).peakResidentSpace path.2.2.2 ≤
          (context base noQuantum N).residentSpace :=
    ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)).trans_eq core
  have reserve : (context base noQuantum N).residentSpace ≤
      (context base noQuantum N).residentSpace + scratchSpace N :=
    fun axis => Nat.le_add_right _ _
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le sourceLimit ?_)
  refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans
    (SpacePool.max_le (storage.trans reserve) ?_)
  exact (Circuit.peakResidentSpace_seq _ _ path.2.2).le.trans
    (SpacePool.max_le (prepared.trans reserve) (allocated.trans reserve))

private lemma redraw_resident
    (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (BitWord.Random.randomCode_peakResidentSpace (execution := model N)
      (sourceRef base noQuantum N) path.1).le.trans (fun axis => Nat.le_add_right _ _)
  · refine (ShorStyle.Canonical.Sampler.Program.samplerProgram_resident_le
      (model := model N) N (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N) path.2).trans ?_
    exact add_le_add (le_refl _) (SpacePool.le_max_left _ _)

/-- The first batch includes every actual resident slot and the sequential scratch maximum. -/
lemma declaredBatch_peakResidentSpace_le
    (path : (code base noQuantum N).Path) :
    (code base noQuantum N).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have bounded := (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le (setup_resident base noQuantum N path.1 path.2.1.1)
      (first_resident base noQuantum N path.2))
  change (code base noQuantum N).peakResidentSpace path ≤ _ at bounded
  rw [declaredBatch_context_residentSpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- A later batch reuses the fixed resident context and the same temporary-space allowance. -/
lemma declaredBatch_next_peakResidentSpace_le
    (path : (nextBatch base noQuantum N).Path) :
    (nextBatch base noQuantum N).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have tail := Circuit.forRange_resident_le 16 (reusedSample base noQuantum N)
    ((context base noQuantum N).residentSpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _) (reused_resident base noQuantum N) path.2
  have bounded := (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le (redraw_resident base noQuantum N path.1) tail)
  change (nextBatch base noQuantum N).peakResidentSpace path ≤ _ at bounded
  rw [declaredBatch_context_residentSpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- The fixed batch context counts its exact auxiliary capacity beside the original caller. -/
lemma declaredBatch_context_auxiliarySpace :
    (context base noQuantum N).auxiliarySpace = retainedSpace N + base.auxiliarySpace := by
  change (Native.context (storageContext base N)
    (storage_empty base noQuantum N) N).auxiliarySpace = _
  rw [declaredSample_context_auxiliarySpace, storageContext, slots_auxiliary, sourceContext,
    ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary]
  unfold retainedSpace
  ac_rfl

private lemma storage_auxiliary_le :
    (storageContext base N).auxiliarySpace ≤ (context base noQuantum N).auxiliarySpace := by
  change (storageContext base N).auxiliarySpace ≤
    (Native.context (storageContext base N) (storage_empty base noQuantum N) N).auxiliarySpace
  rw [declaredSample_context_auxiliarySpace]
  exact fun axis => Nat.le_add_left _ _

private lemma source_auxiliary_le :
    (sourceContext base N).auxiliarySpace ≤ (context base noQuantum N).auxiliarySpace := by
  refine (show (sourceContext base N).auxiliarySpace ≤
    (storageContext base N).auxiliarySpace from ?_).trans
    (storage_auxiliary_le base noQuantum N)
  rw [storageContext, slots_auxiliary]
  exact fun axis => Nat.le_add_left _ _

private lemma copy_auxiliary (index : Fin 16)
    (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).peakAuxiliarySpace path =
      (context base noQuantum N).auxiliarySpace := by
  funext axis
  exact Nat.max_zero _

/-- A reused sample has one live reset bit per wire beyond the complete fixed batch context. -/
lemma declaredBatch_reusedSample_peakAuxiliarySpace (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).peakAuxiliarySpace path =
      resetSpace N + (context base noQuantum N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).trans ?_
  refine (congrArg₂ SpacePool.max
    (declaredReuse_peakAuxiliarySpace (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1)
    (copy_auxiliary base noQuantum N index path.2)).trans ?_
  exact SpacePool.max_eq_left (fun axis => Nat.le_add_left _ _)

private lemma reused_auxiliary (index : Fin 16)
    (path : (reusedSample base noQuantum N index).Path) :
    (reusedSample base noQuantum N index).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  refine (declaredBatch_reusedSample_peakAuxiliarySpace
    base noQuantum N index path).le.trans ?_
  intro axis
  have scratch := SpacePool.le_max_right
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (resetSpace N) axis
  change resetSpace N axis +
    (context base noQuantum N).auxiliarySpace axis ≤
      (context base noQuantum N).auxiliarySpace axis + scratchSpace N axis
  change _ ≤ scratchSpace N axis at scratch
  omega

private lemma first_auxiliary
    (path : (firstBatch base noQuantum N).Path) :
    (firstBatch base noQuantum N).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  have tail := Circuit.forRange_auxiliary_le 15
    (fun index => reusedSample base noQuantum N index.succ)
    ((context base noQuantum N).auxiliarySpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _)
    (fun index => reused_auxiliary base noQuantum N index.succ) path.2
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ tail)
  refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
  · exact (declaredSample_body_peakAuxiliarySpace (storageContext base N)
      (storage_empty base noQuantum N) N (parameter base N) path.1.1).le.trans
        (fun axis => Nat.le_add_right _ _)
  · exact (copy_auxiliary base noQuantum N 0 path.1.2).le.trans
      (fun axis => Nat.le_add_right _ _)

private lemma setup_auxiliary
    (path : (setup base noQuantum N).Path)
    (bodyPath : (body (storageContext base N) (storage_empty base noQuantum N) N
      (parameter base N)).Path) :
    (setup base noQuantum N).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  have source := ShorStyle.Canonical.Sampler.Retained.samplerRetained_auxiliary_le
    (model := model N) base N path.1
  have sourceBudget := ShorStyle.Canonical.Sampler.Retained.auxiliary_budget base N
  have sourceLimit :
      (ShorStyle.Canonical.Sampler.Retained.circuit (model := model N)
        base N).peakAuxiliarySpace path.1 ≤
          (context base noQuantum N).auxiliarySpace + scratchSpace N :=
    source.trans (sourceBudget.symm.trans_le
      (add_le_add (source_auxiliary_le base noQuantum N) (SpacePool.le_max_left _ _)))
  have storage := (slots_peak_auxiliary (execution := model N)
    (sourceContext base N) N path.2.1).trans (storage_auxiliary_le base noQuantum N)
  have core := declaredSample_peakAuxiliarySpace (storageContext base N)
    (storage_empty base noQuantum N) N (parameter base N)
    (path.2.2.1, (path.2.2.2, bodyPath))
  simp only [Declared.code, Circuit.peakAuxiliarySpace_seq] at core
  have prepared :
      (Declared.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).peakAuxiliarySpace path.2.2.1 ≤
          (context base noQuantum N).auxiliarySpace :=
    (SpacePool.le_max_left _ _).trans_eq core
  have allocated :
      (Declared.allocate (storageContext base N)
        (storage_empty base noQuantum N) N).peakAuxiliarySpace path.2.2.2 ≤
          (context base noQuantum N).auxiliarySpace :=
    ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)).trans_eq core
  have reserve : (context base noQuantum N).auxiliarySpace ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N :=
    fun axis => Nat.le_add_right _ _
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le sourceLimit ?_)
  refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans
    (SpacePool.max_le (storage.trans reserve) ?_)
  exact (Circuit.peakAuxiliarySpace_seq _ _ path.2.2).le.trans
    (SpacePool.max_le (prepared.trans reserve) (allocated.trans reserve))

private lemma redraw_auxiliary
    (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (BitWord.Random.randomCode_peakAuxiliarySpace (execution := model N)
      (sourceRef base noQuantum N) path.1).le.trans (fun axis => Nat.le_add_right _ _)
  · refine (ShorStyle.Canonical.Sampler.Program.samplerProgram_auxiliary_le
      (model := model N) N (.storage (sourceRef base noQuantum N).toCStorageRef)
      (parameterRef base noQuantum N) path.2).trans ?_
    exact add_le_add (le_refl _) (SpacePool.le_max_left _ _)

/-- The first batch includes every actual auxiliary slot and the sequential scratch maximum. -/
lemma declaredBatch_peakAuxiliarySpace_le
    (path : (code base noQuantum N).Path) :
    (code base noQuantum N).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have bounded := (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le (setup_auxiliary base noQuantum N path.1 path.2.1.1)
      (first_auxiliary base noQuantum N path.2))
  change (code base noQuantum N).peakAuxiliarySpace path ≤ _ at bounded
  rw [declaredBatch_context_auxiliarySpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- A later batch reuses the fixed auxiliary context and the same temporary-space allowance. -/
lemma declaredBatch_next_peakAuxiliarySpace_le
    (path : (nextBatch base noQuantum N).Path) :
    (nextBatch base noQuantum N).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have tail := Circuit.forRange_auxiliary_le 16 (reusedSample base noQuantum N)
    ((context base noQuantum N).auxiliarySpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _) (reused_auxiliary base noQuantum N) path.2
  have bounded := (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le (redraw_auxiliary base noQuantum N path.1) tail)
  change (nextBatch base noQuantum N).peakAuxiliarySpace path ≤ _ at bounded
  rw [declaredBatch_context_auxiliarySpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
