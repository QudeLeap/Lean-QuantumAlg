/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Live storage of the fixed original oracle batch

The actual source cells, sixteen sample slots, factor result, measurement
cells and working packed result remain in one context with the original bank.
Redraw uses the original classical sampler scratch; a quantum reset uses
one finite classical scratch cell. These scopes run sequentially, so their
uniform allowance is a maximum. Neither scratch nor the fixed slots are
multiplied by the number of samples or later batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

/-- Every retained result representation and the sole original quantum bank are counted. -/
def retainedSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (measurementBits N)) +
    measurementBits N • SpacePool.ofShape (.finite 2) +
      SpacePool.ofQuantumLayout (layout N) +
        (SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
          16 • SpacePool.ofShape (.bits (measurementBits N)) +
            ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))

/-- Sequential source computation and reset share the maximum of their actual scratch budgets. -/
def scratchSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.max (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (SpacePool.ofShape (.finite 2))

/-- A uniform first/later-batch allowance includes the fixed storage and live scratch maximum. -/
def additionalSpace (N : Nat) : SpacePool .quantum := retainedSpace N + scratchSpace N

private theorem samples_resident (ctx : RuntimeCtx .quantum) (width count : Nat) :
    (Slots.samples ctx width count).residentSpace =
      count • SpacePool.ofShape (.bits width) + ctx.residentSpace := by
  induction count with
  | zero => simp only [Slots.samples, zero_nsmul, zero_add]
  | succ count ih =>
      rw [Slots.samples, RuntimeCtx.residentSpace_addRetained, ih, succ_nsmul]
      ac_rfl

private theorem slots_resident (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Slots.context ctx N).residentSpace =
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + ctx.residentSpace := by
  rw [Slots.context, RuntimeCtx.residentSpace_addRetained, samples_resident, add_assoc]

private theorem samples_peak_resident (ctx : RuntimeCtx .quantum) (width count : Nat)
    (path : (Slots.allocateSamples ctx width count).Path) :
    (Slots.allocateSamples ctx width count).peakResidentSpace path ≤
      (Slots.samples ctx width count).residentSpace := by
  induction count with
  | zero =>
      intro axis
      change max (ctx.residentSpace axis) 0 ≤ ctx.residentSpace axis
      omega
  | succ count ih =>
      refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (ih path.1).trans ?_
        change (Slots.samples ctx width count).residentSpace ≤
          SpacePool.ofShape (.bits width) + (Slots.samples ctx width count).residentSpace
        exact fun axis => Nat.le_add_left _ _
      · intro axis
        change max ((Slots.samples ctx width count).residentSpace axis)
          (max ((Slots.samples ctx width (count + 1)).residentSpace axis) 0) ≤
            (Slots.samples ctx width (count + 1)).residentSpace axis
        have growing : (Slots.samples ctx width count).residentSpace axis ≤
            (Slots.samples ctx width (count + 1)).residentSpace axis := Nat.le_add_left _ _
        omega

private theorem slots_peak_resident (ctx : RuntimeCtx .quantum) (N : Nat)
    (path : (Slots.allocate ctx N).Path) :
    (Slots.allocate ctx N).peakResidentSpace path ≤ (Slots.context ctx N).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (samples_peak_resident ctx (measurementBits N) 16 path.1).trans ?_
    exact fun axis => Nat.le_add_left _ _
  · intro axis
    change max ((Slots.samples ctx (measurementBits N) 16).residentSpace axis)
      (max ((Slots.context ctx N).residentSpace axis) 0) ≤ (Slots.context ctx N).residentSpace axis
    have growing : (Slots.samples ctx (measurementBits N) 16).residentSpace axis ≤
        (Slots.context ctx N).residentSpace axis := Nat.le_add_left _ _
    omega

private theorem samples_auxiliary (ctx : RuntimeCtx .quantum) (width count : Nat) :
    (Slots.samples ctx width count).auxiliarySpace =
      count • SpacePool.ofShape (.bits width) + ctx.auxiliarySpace := by
  induction count with
  | zero => simp only [Slots.samples, zero_nsmul, zero_add]
  | succ count ih =>
      rw [Slots.samples, RuntimeCtx.auxiliarySpace_addRetained, ih, succ_nsmul]
      ac_rfl

private theorem slots_auxiliary (ctx : RuntimeCtx .quantum) (N : Nat) :
    (Slots.context ctx N).auxiliarySpace =
      SpacePool.ofShape (.option (.unsignedWord (modulusBits N))) +
        16 • SpacePool.ofShape (.bits (measurementBits N)) + ctx.auxiliarySpace := by
  rw [Slots.context, RuntimeCtx.auxiliarySpace_addRetained, samples_auxiliary, add_assoc]

private theorem samples_peak_auxiliary (ctx : RuntimeCtx .quantum) (width count : Nat)
    (path : (Slots.allocateSamples ctx width count).Path) :
    (Slots.allocateSamples ctx width count).peakAuxiliarySpace path ≤
      (Slots.samples ctx width count).auxiliarySpace := by
  induction count with
  | zero =>
      intro axis
      change max (ctx.auxiliarySpace axis) 0 ≤ ctx.auxiliarySpace axis
      omega
  | succ count ih =>
      refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (ih path.1).trans ?_
        change (Slots.samples ctx width count).auxiliarySpace ≤
          SpacePool.ofShape (.bits width) + (Slots.samples ctx width count).auxiliarySpace
        exact fun axis => Nat.le_add_left _ _
      · intro axis
        change max ((Slots.samples ctx width count).auxiliarySpace axis)
          (max ((Slots.samples ctx width (count + 1)).auxiliarySpace axis) 0) ≤
            (Slots.samples ctx width (count + 1)).auxiliarySpace axis
        have growing : (Slots.samples ctx width count).auxiliarySpace axis ≤
            (Slots.samples ctx width (count + 1)).auxiliarySpace axis := Nat.le_add_left _ _
        omega

private theorem slots_peak_auxiliary (ctx : RuntimeCtx .quantum) (N : Nat)
    (path : (Slots.allocate ctx N).Path) :
    (Slots.allocate ctx N).peakAuxiliarySpace path ≤ (Slots.context ctx N).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (samples_peak_auxiliary ctx (measurementBits N) 16 path.1).trans ?_
    exact fun axis => Nat.le_add_left _ _
  · intro axis
    change max ((Slots.samples ctx (measurementBits N) 16).auxiliarySpace axis)
      (max ((Slots.context ctx N).auxiliarySpace axis) 0) ≤
        (Slots.context ctx N).auxiliarySpace axis
    have growing : (Slots.samples ctx (measurementBits N) 16).auxiliarySpace axis ≤
        (Slots.context ctx N).auxiliarySpace axis := Nat.le_add_left _ _
    omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The fixed batch context counts its exact resident capacity beside the original caller. -/
theorem nativeOracle_batch_context_residentSpace :
    (context base noQuantum N).residentSpace = retainedSpace N + base.residentSpace := by
  change (Native.context (storageContext base N)
    (storage_empty base noQuantum N) N).residentSpace = _
  rw [nativeOracle_context_residentSpace, storageContext, slots_resident, sourceContext,
    ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident]
  unfold retainedSpace
  ac_rfl

private theorem storage_resident_le :
    (storageContext base N).residentSpace ≤ (context base noQuantum N).residentSpace := by
  change (storageContext base N).residentSpace ≤
    (Native.context (storageContext base N) (storage_empty base noQuantum N) N).residentSpace
  rw [nativeOracle_context_residentSpace]
  exact fun axis => Nat.le_add_left _ _

private theorem source_resident_le :
    (sourceContext base N).residentSpace ≤ (context base noQuantum N).residentSpace := by
  refine (show (sourceContext base N).residentSpace ≤
    (storageContext base N).residentSpace from ?_).trans
    (storage_resident_le base noQuantum N)
  rw [storageContext, slots_resident]
  exact fun axis => Nat.le_add_left _ _

private theorem copy_resident (index : Fin 16) (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).peakResidentSpace path =
      (context base noQuantum N).residentSpace := by
  funext axis
  exact Nat.max_zero _

private theorem reused_resident (input : Input N) (index : Fin 16)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · have actual := nativeOracle_reuse_peakResidentSpace (storageContext base N)
      (storage_empty base noQuantum N) N input (parameter base N) path.1
    refine actual.le.trans ?_
    intro axis
    have scratch := SpacePool.le_max_right
      (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
      (SpacePool.ofShape (.finite 2)) axis
    change SpacePool.ofShape (kind := .quantum) (.finite 2) axis +
      (context base noQuantum N).residentSpace axis ≤
        (context base noQuantum N).residentSpace axis + scratchSpace N axis
    change _ ≤ scratchSpace N axis at scratch
    omega
  · exact (copy_resident base noQuantum N index path.2).le.trans (fun axis => Nat.le_add_right _ _)

private theorem first_resident (input : Input N)
    (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  have tail := Circuit.forRange_resident_le 15
    (fun index => reusedSample base noQuantum N input index.succ)
    ((context base noQuantum N).residentSpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _)
    (fun index => reused_resident base noQuantum N input index.succ) path.2
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ tail)
  refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
  · exact (body_resident (storageContext base N) (storage_empty base noQuantum N) N
      input (parameter base N) path.1.1).le.trans (fun axis => Nat.le_add_right _ _)
  · exact (copy_resident base noQuantum N 0 path.1.2).le.trans (fun axis => Nat.le_add_right _ _)

private theorem setup_resident (input : Input N) (path : (setup base noQuantum N).Path)
    (bodyPath : (body (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).Path) :
    (setup base noQuantum N).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  have source := ShorStyle.Canonical.Sampler.Retained.samplerRetained_resident_le base N path.1
  have sourceBudget := ShorStyle.Canonical.Sampler.Retained.resident_budget base N
  have sourceIncluded := source_resident_le base noQuantum N
  have storage := (slots_peak_resident (sourceContext base N) N path.2.1).trans
    (storage_resident_le base noQuantum N)
  have core := nativeOracle_peakResidentSpace (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N)
    (path.2.2.1, (path.2.2.2, bodyPath))
  simp only [Native.code, Circuit.peakResidentSpace_seq] at core
  have outer := Circuit.peakResidentSpace_seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    ((Slots.allocate (sourceContext base N) N).seq
      ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
        (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N))) path
  have middle := Circuit.peakResidentSpace_seq (Slots.allocate (sourceContext base N) N)
    ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
      (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)) path.2
  have last := Circuit.peakResidentSpace_seq
    (Native.prepare (storageContext base N) (storage_empty base noQuantum N) N)
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N) path.2.2
  intro axis
  have outerAxis := congrFun outer axis
  have middleAxis := congrFun middle axis
  have lastAxis := congrFun last axis
  change (setup base noQuantum N).peakResidentSpace path axis = _ at outerAxis
  have sourceAxis := source axis
  have includedAxis := sourceIncluded axis
  have sourceBudgetAxis := congrFun sourceBudget axis
  have storageAxis := storage axis
  have coreAxis := congrFun core axis
  have scratch := SpacePool.le_max_left
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (SpacePool.ofShape (.finite 2)) axis
  change _ ≤ scratchSpace N axis at scratch
  simp only [SpacePool.max, Pi.add_apply] at coreAxis sourceAxis sourceBudgetAxis
  simp only [SpacePool.max, Pi.add_apply] at outerAxis middleAxis lastAxis ⊢
  change (sourceContext base N).residentSpace axis +
    ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N) axis =
      base.residentSpace axis +
        ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis
    at sourceBudgetAxis
  change (ShorStyle.Canonical.Sampler.Retained.circuit base N).peakResidentSpace path.1 axis ≤
    base.residentSpace axis +
      ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis
    at sourceAxis
  change _ = (context base noQuantum N).residentSpace axis at coreAxis
  have sourceLimit :
      (ShorStyle.Canonical.Sampler.Retained.circuit base N).peakResidentSpace path.1 axis ≤
        (context base noQuantum N).residentSpace axis + scratchSpace N axis :=
    sourceAxis.trans (sourceBudgetAxis.symm.trans_le (Nat.add_le_add includedAxis scratch))
  have prepared :
      (Native.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).peakResidentSpace path.2.2.1 axis ≤
          (context base noQuantum N).residentSpace axis :=
    (Nat.le_max_left _ _).trans_eq coreAxis
  have allocated :
      (Native.allocate (storageContext base N)
        (storage_empty base noQuantum N) N).peakResidentSpace path.2.2.2 axis ≤
          (context base noQuantum N).residentSpace axis :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans_eq coreAxis
  have reserve := Nat.le_add_right
    ((context base noQuantum N).residentSpace axis) (scratchSpace N axis)
  have finalLimit := lastAxis.trans_le
    (max_le (prepared.trans reserve) (allocated.trans reserve))
  have middleLimit := middleAxis.trans_le (max_le (storageAxis.trans reserve) finalLimit)
  exact outerAxis.trans_le (max_le sourceLimit middleLimit)

private theorem redraw_resident (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).peakResidentSpace path ≤
      (context base noQuantum N).residentSpace + scratchSpace N := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max ((context base noQuantum N).residentSpace axis) 0 ≤ _ + _
    omega
  · refine (ShorStyle.Canonical.Sampler.Program.samplerProgram_resident_le N
      (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N)
      path.2).trans ?_
    exact add_le_add (le_refl _) (SpacePool.le_max_left _ _)

/-- The first batch includes every actual resident slot and the sequential scratch maximum. -/
theorem nativeOracle_batch_peakResidentSpace_le (input : Input N)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have bounded := (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le (setup_resident base noQuantum N input path.1 path.2.1.1)
      (first_resident base noQuantum N input path.2))
  change (code base noQuantum N input).peakResidentSpace path ≤ _ at bounded
  rw [nativeOracle_batch_context_residentSpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- A later batch reuses the fixed resident context and the same temporary-space allowance. -/
theorem nativeOracle_nextBatch_peakResidentSpace_le (input : Input N)
    (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have tail := Circuit.forRange_resident_le 16 (reusedSample base noQuantum N input)
    ((context base noQuantum N).residentSpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _) (reused_resident base noQuantum N input) path.2
  have bounded := (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le (redraw_resident base noQuantum N path.1) tail)
  change (nextBatch base noQuantum N input).peakResidentSpace path ≤ _ at bounded
  rw [nativeOracle_batch_context_residentSpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- The fixed batch context counts its exact auxiliary capacity beside the original caller. -/
theorem nativeOracle_batch_context_auxiliarySpace :
    (context base noQuantum N).auxiliarySpace = retainedSpace N + base.auxiliarySpace := by
  change (Native.context (storageContext base N)
    (storage_empty base noQuantum N) N).auxiliarySpace = _
  rw [nativeOracle_context_auxiliarySpace, storageContext, slots_auxiliary, sourceContext,
    ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary]
  unfold retainedSpace
  ac_rfl

private theorem storage_auxiliary_le :
    (storageContext base N).auxiliarySpace ≤ (context base noQuantum N).auxiliarySpace := by
  change (storageContext base N).auxiliarySpace ≤
    (Native.context (storageContext base N) (storage_empty base noQuantum N) N).auxiliarySpace
  rw [nativeOracle_context_auxiliarySpace]
  exact fun axis => Nat.le_add_left _ _

private theorem source_auxiliary_le :
    (sourceContext base N).auxiliarySpace ≤ (context base noQuantum N).auxiliarySpace := by
  refine (show (sourceContext base N).auxiliarySpace ≤
    (storageContext base N).auxiliarySpace from ?_).trans
    (storage_auxiliary_le base noQuantum N)
  rw [storageContext, slots_auxiliary]
  exact fun axis => Nat.le_add_left _ _

private theorem copy_auxiliary (index : Fin 16) (path : (copy base noQuantum N index).Path) :
    (copy base noQuantum N index).peakAuxiliarySpace path =
      (context base noQuantum N).auxiliarySpace := by
  funext axis
  exact Nat.max_zero _

private theorem reused_auxiliary (input : Input N) (index : Fin 16)
    (path : (reusedSample base noQuantum N input index).Path) :
    (reusedSample base noQuantum N input index).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · have actual := nativeOracle_reuse_peakAuxiliarySpace (storageContext base N)
      (storage_empty base noQuantum N) N input (parameter base N) path.1
    refine actual.le.trans ?_
    intro axis
    have scratch := SpacePool.le_max_right
      (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
      (SpacePool.ofShape (.finite 2)) axis
    change SpacePool.ofShape (kind := .quantum) (.finite 2) axis +
      (context base noQuantum N).auxiliarySpace axis ≤
        (context base noQuantum N).auxiliarySpace axis + scratchSpace N axis
    change _ ≤ scratchSpace N axis at scratch
    omega
  · exact (copy_auxiliary base noQuantum N index path.2).le.trans (fun axis => Nat.le_add_right _ _)

private theorem first_auxiliary (input : Input N)
    (path : (firstBatch base noQuantum N input).Path) :
    (firstBatch base noQuantum N input).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  have tail := Circuit.forRange_auxiliary_le 15
    (fun index => reusedSample base noQuantum N input index.succ)
    ((context base noQuantum N).auxiliarySpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _)
    (fun index => reused_auxiliary base noQuantum N input index.succ) path.2
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ tail)
  refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
  · exact (body_auxiliary (storageContext base N) (storage_empty base noQuantum N) N
      input (parameter base N) path.1.1).le.trans (fun axis => Nat.le_add_right _ _)
  · exact (copy_auxiliary base noQuantum N 0 path.1.2).le.trans (fun axis => Nat.le_add_right _ _)

private theorem setup_auxiliary (input : Input N) (path : (setup base noQuantum N).Path)
    (bodyPath : (body (storageContext base N) (storage_empty base noQuantum N) N input
      (parameter base N)).Path) :
    (setup base noQuantum N).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  have source := ShorStyle.Canonical.Sampler.Retained.samplerRetained_auxiliary_le base N path.1
  have sourceBudget := ShorStyle.Canonical.Sampler.Retained.auxiliary_budget base N
  have sourceIncluded := source_auxiliary_le base noQuantum N
  have storage := (slots_peak_auxiliary (sourceContext base N) N path.2.1).trans
    (storage_auxiliary_le base noQuantum N)
  have core := nativeOracle_peakAuxiliarySpace (storageContext base N)
    (storage_empty base noQuantum N) N input (parameter base N)
    (path.2.2.1, (path.2.2.2, bodyPath))
  simp only [Native.code, Circuit.peakAuxiliarySpace_seq] at core
  have outer := Circuit.peakAuxiliarySpace_seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    ((Slots.allocate (sourceContext base N) N).seq
      ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
        (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N))) path
  have middle := Circuit.peakAuxiliarySpace_seq (Slots.allocate (sourceContext base N) N)
    ((Native.prepare (storageContext base N) (storage_empty base noQuantum N) N).seq
      (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N)) path.2
  have last := Circuit.peakAuxiliarySpace_seq
    (Native.prepare (storageContext base N) (storage_empty base noQuantum N) N)
    (Native.allocate (storageContext base N) (storage_empty base noQuantum N) N) path.2.2
  intro axis
  have outerAxis := congrFun outer axis
  have middleAxis := congrFun middle axis
  have lastAxis := congrFun last axis
  change (setup base noQuantum N).peakAuxiliarySpace path axis = _ at outerAxis
  have sourceAxis := source axis
  have includedAxis := sourceIncluded axis
  have sourceBudgetAxis := congrFun sourceBudget axis
  have storageAxis := storage axis
  have coreAxis := congrFun core axis
  have scratch := SpacePool.le_max_left
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (SpacePool.ofShape (.finite 2)) axis
  change _ ≤ scratchSpace N axis at scratch
  simp only [SpacePool.max, Pi.add_apply] at coreAxis sourceAxis sourceBudgetAxis
  simp only [SpacePool.max, Pi.add_apply] at outerAxis middleAxis lastAxis ⊢
  change (sourceContext base N).auxiliarySpace axis +
    ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N) axis =
      base.auxiliarySpace axis +
        ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis
    at sourceBudgetAxis
  change (ShorStyle.Canonical.Sampler.Retained.circuit base N).peakAuxiliarySpace path.1 axis ≤
    base.auxiliarySpace axis +
      ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis
    at sourceAxis
  change _ = (context base noQuantum N).auxiliarySpace axis at coreAxis
  have sourceLimit :
      (ShorStyle.Canonical.Sampler.Retained.circuit base N).peakAuxiliarySpace path.1 axis ≤
        (context base noQuantum N).auxiliarySpace axis + scratchSpace N axis :=
    sourceAxis.trans (sourceBudgetAxis.symm.trans_le (Nat.add_le_add includedAxis scratch))
  have prepared :
      (Native.prepare (storageContext base N)
        (storage_empty base noQuantum N) N).peakAuxiliarySpace path.2.2.1 axis ≤
          (context base noQuantum N).auxiliarySpace axis :=
    (Nat.le_max_left _ _).trans_eq coreAxis
  have allocated :
      (Native.allocate (storageContext base N)
        (storage_empty base noQuantum N) N).peakAuxiliarySpace path.2.2.2 axis ≤
          (context base noQuantum N).auxiliarySpace axis :=
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _)).trans_eq coreAxis
  have reserve := Nat.le_add_right
    ((context base noQuantum N).auxiliarySpace axis) (scratchSpace N axis)
  have finalLimit := lastAxis.trans_le
    (max_le (prepared.trans reserve) (allocated.trans reserve))
  have middleLimit := middleAxis.trans_le (max_le (storageAxis.trans reserve) finalLimit)
  exact outerAxis.trans_le (max_le sourceLimit middleLimit)

private theorem redraw_auxiliary (path : (redraw base noQuantum N).Path) :
    (redraw base noQuantum N).peakAuxiliarySpace path ≤
      (context base noQuantum N).auxiliarySpace + scratchSpace N := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · intro axis
    change max ((context base noQuantum N).auxiliarySpace axis) 0 ≤ _ + _
    omega
  · refine (ShorStyle.Canonical.Sampler.Program.samplerProgram_auxiliary_le N
      (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N)
      path.2).trans ?_
    exact add_le_add (le_refl _) (SpacePool.le_max_left _ _)

/-- The first batch includes every actual auxiliary slot and the sequential scratch maximum. -/
theorem nativeOracle_batch_peakAuxiliarySpace_le (input : Input N)
    (path : (code base noQuantum N input).Path) :
    (code base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have bounded := (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le (setup_auxiliary base noQuantum N input path.1 path.2.1.1)
      (first_auxiliary base noQuantum N input path.2))
  change (code base noQuantum N input).peakAuxiliarySpace path ≤ _ at bounded
  rw [nativeOracle_batch_context_auxiliarySpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

/-- A later batch reuses the fixed auxiliary context and the same temporary-space allowance. -/
theorem nativeOracle_nextBatch_peakAuxiliarySpace_le (input : Input N)
    (path : (nextBatch base noQuantum N input).Path) :
    (nextBatch base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have tail := Circuit.forRange_auxiliary_le 16 (reusedSample base noQuantum N input)
    ((context base noQuantum N).auxiliarySpace + scratchSpace N)
    (fun axis => Nat.le_add_right _ _) (reused_auxiliary base noQuantum N input) path.2
  have bounded := (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le (redraw_auxiliary base noQuantum N path.1) tail)
  change (nextBatch base noQuantum N input).peakAuxiliarySpace path ≤ _ at bounded
  rw [nativeOracle_batch_context_auxiliarySpace] at bounded
  simpa only [additionalSpace, add_assoc, add_comm, add_left_comm] using bounded

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
