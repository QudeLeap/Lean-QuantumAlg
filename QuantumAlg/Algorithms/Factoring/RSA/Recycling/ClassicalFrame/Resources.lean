/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Allocation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Exact simultaneous capacity of the preallocated recycled factoring frame

All batch storage is simultaneously live before the bank is prepared. The
space formula therefore counts every future source and outcome cell already
at that point. Sampler and recovery temporary work is not included here: their
later execution must add its actual simultaneous scratch to this fixed frame.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame

noncomputable section

variable [configuration : Configuration]

open Execution ShortDLP.CompiledMAU
open EkeraHastadStyle.Canonical

/-- Independent capacity of one source pair, configured packed outcomes, and its factor. -/
def batchSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.ofShape (.bits (residueSamplingBits N)) + SpacePool.ofShape (ParameterShape N) +
    membersPerBatch • SpacePool.ofShape (.bits (measurementBits N)) +
      SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N)

/-- All batches and the distinct final selected-factor destination are live together. -/
def frameSpace (N count : Nat) : SpacePool .quantum :=
  count • batchSpace N + SpacePool.ofShape (LatticeBatchRecoveryOutput.OutputShape N)

/-- The exact binary capacity includes complete parameter flags and every optional-factor tag. -/
def classicalBits (N count : Nat) : Nat :=
  count * (19 * modulusBits N + membersPerBatch * measurementBits N + 2) + modulusBits N + 1

omit configuration in
private lemma sampler_resultSpace (N : Nat) :
    ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (ShorStyle.Canonical.modulusBits N) =
      SpacePool.ofShape (.bits (residueSamplingBits N)) + SpacePool.ofShape (ParameterShape N) := by
  apply SpacePool.ext
  intro axis
  cases axis with
  | classicalBits =>
      simp [ShorStyle.Canonical.Sampler.Retained.resultSpace, ParameterShape,
        ShorStyle.Canonical.ParameterShape, residueSamplingBits,
        ShorStyle.Canonical.residueSamplingBits, ShorStyle.Canonical.residueProposalCount,
        SpacePool.ofShape, modulusBits]
      omega
  | quantumSystems dimension =>
      simp [ShorStyle.Canonical.Sampler.Retained.resultSpace, ParameterShape,
        ShorStyle.Canonical.ParameterShape, SpacePool.ofShape]

/-- A batch's actual resident capacity is precisely the sum of its retained shapes. -/
lemma rsaRecyclingFrame_batch_resident (base : RuntimeCtx .quantum) (N : Nat) :
    (batch base N).residentSpace = batchSpace N + base.residentSpace := by
  rw [batch, RuntimeCtx.residentSpace_addRetained, outcomes,
    RuntimeResults.shortDLP_runtimeResults_resident]
  rw [sampled, ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident,
    sampler_resultSpace]
  unfold batchSpace
  ac_rfl

/-- Every retained source and result cell also keeps its real auxiliary role. -/
lemma rsaRecyclingFrame_batch_auxiliary (base : RuntimeCtx .quantum) (N : Nat) :
    (batch base N).auxiliarySpace = batchSpace N + base.auxiliarySpace := by
  rw [batch, RuntimeCtx.auxiliarySpace_addRetained, outcomes,
    RuntimeResults.shortDLP_runtimeResults_auxiliary]
  rw [sampled, ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary,
    sampler_resultSpace]
  unfold batchSpace
  ac_rfl

/-- All chronological batch frames retain their full simultaneous resident capacity. -/
lemma rsaRecyclingFrame_batches_resident (N : Nat) (base : RuntimeCtx .quantum) (count : Nat) :
    (batches N base count).residentSpace = count • batchSpace N + base.residentSpace := by
  induction count generalizing base with
  | zero => simp only [batches, zero_nsmul, zero_add]
  | succ count ih =>
      rw [batches, ih, rsaRecyclingFrame_batch_resident, succ_nsmul]
      ac_rfl

/-- All actual retained roles contribute to auxiliary space at the same time. -/
lemma rsaRecyclingFrame_batches_auxiliary (N : Nat) (base : RuntimeCtx .quantum) (count : Nat) :
    (batches N base count).auxiliarySpace = count • batchSpace N + base.auxiliarySpace := by
  induction count generalizing base with
  | zero => simp only [batches, zero_nsmul, zero_add]
  | succ count ih =>
      rw [batches, ih, rsaRecyclingFrame_batch_auxiliary, succ_nsmul]
      ac_rfl

/-- The full frame adds no capacity beyond the explicitly retained shapes. -/
lemma rsaRecyclingFrame_context_resident (base : RuntimeCtx .quantum) (N count : Nat) :
    (context base N count).residentSpace = frameSpace N count + base.residentSpace := by
  rw [context, RuntimeCtx.residentSpace_addRetained, rsaRecyclingFrame_batches_resident]
  unfold frameSpace
  ac_rfl

/-- The full retained frame has the identical exact auxiliary-capacity increment. -/
lemma rsaRecyclingFrame_context_auxiliary (base : RuntimeCtx .quantum) (N count : Nat) :
    (context base N count).auxiliarySpace = frameSpace N count + base.auxiliarySpace := by
  rw [context, RuntimeCtx.auxiliarySpace_addRetained, rsaRecyclingFrame_batches_auxiliary]
  unfold frameSpace
  ac_rfl

/-- The shape-based formula equals its independent closed binary-capacity expression. -/
lemma rsaRecyclingFrame_frameSpace_eq (N count : Nat) :
    frameSpace N count = SpacePool.ofShape (.bits (classicalBits N count)) := by
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [frameSpace, batchSpace, classicalBits, ParameterShape,
      ShorStyle.Canonical.ParameterShape, residueSamplingBits,
      ShorStyle.Canonical.residueSamplingBits, ShorStyle.Canonical.residueProposalCount,
      LatticeBatchRecoveryOutput.OutputShape, SpacePool.ofShape, modulusBits]; ring

/-- Before the quantum allocation the exact classical frame is already resident. -/
lemma rsaRecyclingFrame_resident_classicalBits (base : RuntimeCtx .quantum) (N count : Nat) :
    (context base N count).residentSpace .classicalBits =
      classicalBits N count + base.residentSpace .classicalBits := by
  rw [rsaRecyclingFrame_context_resident, rsaRecyclingFrame_frameSpace_eq]
  rfl

/-- Auxiliary accounting includes every preallocated source, packed result, and factor. -/
lemma rsaRecyclingFrame_auxiliary_classicalBits (base : RuntimeCtx .quantum) (N count : Nat) :
    (context base N count).auxiliarySpace .classicalBits =
      classicalBits N count + base.auxiliarySpace .classicalBits := by
  rw [rsaRecyclingFrame_context_auxiliary, rsaRecyclingFrame_frameSpace_eq]
  rfl

omit configuration in
/-- Allocating packed destinations peaks at their actual final retained context. -/
lemma rsaRecyclingFrame_allocatePacked_resident (m ell width : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocatePacked m ell width base count).Path) :
    (allocatePacked m ell width base count).peakResidentSpace path =
      (RuntimeResults.context m ell width base count).residentSpace := by
  induction count generalizing base with
  | zero => exact Circuit.peakResidentSpace_id path
  | succ count ih =>
      have joined := Circuit.peakResidentSpace_seq
        (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
          base base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
          base.canonicalFreshKey_fresh)
        (allocatePacked m ell width (RuntimeResults.next m ell width base) count) path
      have normalized := joined.trans (congrArg₂ SpacePool.max
        (Circuit.peakResidentSpace_retain
          (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := base)
          base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
          base.canonicalFreshKey_fresh path.1)
        (ih (RuntimeResults.next m ell width base) path.2))
      apply normalized.trans
      apply SpacePool.max_eq_right
      rw [RuntimeResults.shortDLP_runtimeResults_resident]
      exact le_add_of_nonneg_left zero_le

omit configuration in
/-- Packed-cell auxiliary peak equals the same actual final retained roles. -/
lemma rsaRecyclingFrame_allocatePacked_auxiliary (m ell width : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocatePacked m ell width base count).Path) :
    (allocatePacked m ell width base count).peakAuxiliarySpace path =
      (RuntimeResults.context m ell width base count).auxiliarySpace := by
  induction count generalizing base with
  | zero => exact Circuit.peakAuxiliarySpace_id path
  | succ count ih =>
      have joined := Circuit.peakAuxiliarySpace_seq
        (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
          base base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
          base.canonicalFreshKey_fresh)
        (allocatePacked m ell width (RuntimeResults.next m ell width base) count) path
      have normalized := joined.trans (congrArg₂ SpacePool.max
        (Circuit.peakAuxiliarySpace_retain
          (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := base)
          base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
          base.canonicalFreshKey_fresh path.1)
        (ih (RuntimeResults.next m ell width base) path.2))
      apply normalized.trans
      apply SpacePool.max_eq_right
      rw [RuntimeResults.shortDLP_runtimeResults_auxiliary]
      exact le_add_of_nonneg_left zero_le

private lemma sampled_resident_le (base : RuntimeCtx .quantum) (N : Nat) :
    (sampled base N).residentSpace ≤ (batch base N).residentSpace := by
  rw [batch, RuntimeCtx.residentSpace_addRetained, outcomes,
    RuntimeResults.shortDLP_runtimeResults_resident]
  exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)

private lemma sampled_auxiliary_le (base : RuntimeCtx .quantum) (N : Nat) :
    (sampled base N).auxiliarySpace ≤ (batch base N).auxiliarySpace := by
  rw [batch, RuntimeCtx.auxiliarySpace_addRetained, outcomes,
    RuntimeResults.shortDLP_runtimeResults_auxiliary]
  exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_left zero_le)

/-- One batch allocation reaches exactly the final live resident context. -/
lemma rsaRecyclingFrame_allocateBatch_resident (base : RuntimeCtx .quantum) (N : Nat)
    (path : (allocateBatch base N).Path) :
    (allocateBatch base N).peakResidentSpace path = (batch base N).residentSpace := by
  apply le_antisymm ?_ ((allocateBatch base N).output_residentSpace_le_peak path)
  have joined := Circuit.peakResidentSpace_seq
    (ShorStyle.Canonical.Sampler.Retained.allocation
      (model := ShortDLP.CompiledMAU.Recycling.model) base N)
    ((allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N)
      membersPerBatch).seq
      (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
        (outcomes base N) (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh)) path
  apply joined.le.trans
  apply SpacePool.max_le
  · exact (ShorStyle.Canonical.Sampler.Retained.samplerRetained_allocation_resident_le
      (model := ShortDLP.CompiledMAU.Recycling.model) base N path.1).trans
        (sampled_resident_le base N)
  · have tail := Circuit.peakResidentSpace_seq
      (allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N)
        membersPerBatch)
      (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
        (outcomes base N) (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh)
      path.2
    have normalized := tail.trans (congrArg₂ SpacePool.max
      (rsaRecyclingFrame_allocatePacked_resident
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch
          path.2.1)
      (Circuit.peakResidentSpace_retain
        (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := outcomes base N)
        (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        (outcomes base N).canonicalFreshKey_fresh path.2.2))
    apply normalized.le.trans
    apply SpacePool.max_le _ le_rfl
    change (outcomes base N).residentSpace ≤
      ((outcomes base N).addRetained (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N)
        (outcomes base N).canonicalFreshKey_fresh).residentSpace
    rw [RuntimeCtx.residentSpace_addRetained]
    exact le_add_of_nonneg_left zero_le

/-- One batch allocation reaches exactly the complete final auxiliary roles. -/
lemma rsaRecyclingFrame_allocateBatch_auxiliary (base : RuntimeCtx .quantum) (N : Nat)
    (path : (allocateBatch base N).Path) :
    (allocateBatch base N).peakAuxiliarySpace path = (batch base N).auxiliarySpace := by
  apply le_antisymm ?_ ((allocateBatch base N).output_auxiliarySpace_le_peak path)
  have joined := Circuit.peakAuxiliarySpace_seq
    (ShorStyle.Canonical.Sampler.Retained.allocation
      (model := ShortDLP.CompiledMAU.Recycling.model) base N)
    ((allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N)
      membersPerBatch).seq
      (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
        (outcomes base N) (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh)) path
  apply joined.le.trans
  apply SpacePool.max_le
  · exact (ShorStyle.Canonical.Sampler.Retained.samplerRetained_allocation_auxiliary_le
      (model := ShortDLP.CompiledMAU.Recycling.model) base N path.1).trans
        (sampled_auxiliary_le base N)
  · have tail := Circuit.peakAuxiliarySpace_seq
      (allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N)
        membersPerBatch)
      (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
        (outcomes base N) (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh)
      path.2
    have normalized := tail.trans (congrArg₂ SpacePool.max
      (rsaRecyclingFrame_allocatePacked_auxiliary
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch
          path.2.1)
      (Circuit.peakAuxiliarySpace_retain
        (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := outcomes base N)
        (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
        (outcomes base N).canonicalFreshKey_fresh path.2.2))
    apply normalized.le.trans
    apply SpacePool.max_le _ le_rfl
    change (outcomes base N).auxiliarySpace ≤
      ((outcomes base N).addRetained (outcomes base N).canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N)
        (outcomes base N).canonicalFreshKey_fresh).auxiliarySpace
    rw [RuntimeCtx.auxiliarySpace_addRetained]
    exact le_add_of_nonneg_left zero_le

/-- Every batch destination is live at the actual preallocation resident peak. -/
lemma rsaRecyclingFrame_allocateBatches_resident (N : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocateBatches N base count).Path) :
    (allocateBatches N base count).peakResidentSpace path =
      (batches N base count).residentSpace := by
  induction count generalizing base with
  | zero => exact Circuit.peakResidentSpace_id path
  | succ count ih =>
      have joined := Circuit.peakResidentSpace_seq (allocateBatch base N)
        (allocateBatches N (batch base N) count) path
      have normalized := joined.trans (congrArg₂ SpacePool.max
        (rsaRecyclingFrame_allocateBatch_resident base N path.1)
        (ih (batch base N) path.2))
      apply normalized.trans
      apply SpacePool.max_eq_right
      rw [rsaRecyclingFrame_batches_resident]
      exact le_add_of_nonneg_left zero_le

/-- The same complete batch family contributes to the actual auxiliary peak. -/
lemma rsaRecyclingFrame_allocateBatches_auxiliary (N : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    (path : (allocateBatches N base count).Path) :
    (allocateBatches N base count).peakAuxiliarySpace path =
      (batches N base count).auxiliarySpace := by
  induction count generalizing base with
  | zero => exact Circuit.peakAuxiliarySpace_id path
  | succ count ih =>
      have joined := Circuit.peakAuxiliarySpace_seq (allocateBatch base N)
        (allocateBatches N (batch base N) count) path
      have normalized := joined.trans (congrArg₂ SpacePool.max
        (rsaRecyclingFrame_allocateBatch_auxiliary base N path.1)
        (ih (batch base N) path.2))
      apply normalized.trans
      apply SpacePool.max_eq_right
      rw [rsaRecyclingFrame_batches_auxiliary]
      exact le_add_of_nonneg_left zero_le

/-- Full preallocation has exact resident peak, rather than the old lazy allocation peak. -/
lemma rsaRecyclingFrame_allocate_resident (base : RuntimeCtx .quantum) (N count : Nat)
    (path : (allocate base N count).Path) :
    (allocate base N count).peakResidentSpace path = frameSpace N count + base.residentSpace := by
  have joined := Circuit.peakResidentSpace_seq (allocateBatches N base count)
    (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
      (batches N base count) (batches N base count).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N)
      (batches N base count).canonicalFreshKey_fresh) path
  have normalized := joined.trans (congrArg₂ SpacePool.max
    (rsaRecyclingFrame_allocateBatches_resident N base count path.1)
    (Circuit.peakResidentSpace_retain
      (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := batches N base count)
      (batches N base count).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      (batches N base count).canonicalFreshKey_fresh path.2))
  have ordered : (batches N base count).residentSpace ≤ (context base N count).residentSpace := by
    rw [context, RuntimeCtx.residentSpace_addRetained]
    exact le_add_of_nonneg_left zero_le
  exact (normalized.trans (SpacePool.max_eq_right ordered)).trans
    (rsaRecyclingFrame_context_resident base N count)

/-- Full preallocation has exact auxiliary peak for the same actual retention program. -/
lemma rsaRecyclingFrame_allocate_auxiliary (base : RuntimeCtx .quantum) (N count : Nat)
    (path : (allocate base N count).Path) :
    (allocate base N count).peakAuxiliarySpace path = frameSpace N count + base.auxiliarySpace := by
  have joined := Circuit.peakAuxiliarySpace_seq (allocateBatches N base count)
    (Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
      (batches N base count) (batches N base count).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N)
      (batches N base count).canonicalFreshKey_fresh) path
  have normalized := joined.trans (congrArg₂ SpacePool.max
    (rsaRecyclingFrame_allocateBatches_auxiliary N base count path.1)
    (Circuit.peakAuxiliarySpace_retain
      (model := ShortDLP.CompiledMAU.Recycling.model) (ctx := batches N base count)
      (batches N base count).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      (batches N base count).canonicalFreshKey_fresh path.2))
  have ordered : (batches N base count).auxiliarySpace ≤ (context base N count).auxiliarySpace := by
    rw [context, RuntimeCtx.auxiliarySpace_addRetained]
    exact le_add_of_nonneg_left zero_le
  exact (normalized.trans (SpacePool.max_eq_right ordered)).trans
    (rsaRecyclingFrame_context_auxiliary base N count)

end

end QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame
