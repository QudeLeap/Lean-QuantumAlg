/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Configuration

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results.Laws
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# All classical batch destinations before the sole recycled quantum bank

Each chronological batch owns a source sample, the complete sampled parameter,
configured distinct packed observations, and a recovery factor. A separate final
cell receives the first successful factor. The allocation order is independent
of sampling: retaining these cells initializes storage and does not draw any
future source sample. Every member can therefore use one fixed recycling
context without extending that context between members or batches.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame

noncomputable section

variable [configuration : Configuration]

open Execution ShortDLP.CompiledMAU
open EkeraHastadStyle.Canonical

/-- The actual source pair, before retaining this batch's packed observations. -/
def sampled (base : RuntimeCtx .quantum) (N : Nat) : RuntimeCtx .quantum :=
  ShorStyle.Canonical.Sampler.Retained.context base N

/-- Configured chronological destinations use the existing packed-result layout. -/
def outcomes (base : RuntimeCtx .quantum) (N : Nat) : RuntimeCtx .quantum :=
  RuntimeResults.context (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sampled base N) membersPerBatch

/-- One batch retains its complete source, observations, and independent factor result. -/
def batch (base : RuntimeCtx .quantum) (N : Nat) : RuntimeCtx .quantum :=
  (outcomes base N).addRetained (outcomes base N).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh

/-- Earlier writable cells cross the two source allocations without copying their values. -/
def sampledWrite {base : RuntimeCtx .quantum} {shape : CShape} (N : Nat)
    (ref : CWriteRef base shape) : CWriteRef (sampled base N) shape :=
  (ref.underRetained base.canonicalFreshKey (.bits (residueSamplingBits N))
    base.canonicalFreshKey_fresh).underRetained
      (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey
      (ParameterShape N)
      (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey_fresh

/-- A writable source cell stays below every packed destination and the batch factor. -/
def finishWrite {base : RuntimeCtx .quantum} {shape : CShape} (N : Nat)
    (ref : CWriteRef (sampled base N) shape) : CWriteRef (batch base N) shape :=
  (RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    ref membersPerBatch).underRetained (outcomes base N).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh

/-- Existing writable storage remains the same physical storage after one complete batch frame. -/
def batchWrite {base : RuntimeCtx .quantum} {shape : CShape} (N : Nat)
    (ref : CWriteRef base shape) : CWriteRef (batch base N) shape :=
  finishWrite N (sampledWrite N ref)

/-- Existing structural input crosses only actual classical retention instructions. -/
def batchInput {base : RuntimeCtx .quantum} {shape : CShape} (N : Nat)
    (input : CInputRef base shape) : CInputRef (batch base N) shape :=
  (RuntimeResults.liftInput (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) input) membersPerBatch).underRetained
      (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      (outcomes base N).canonicalFreshKey_fresh

/-- Source sample retained for this batch, with its original complete bit width. -/
def batchSample (base : RuntimeCtx .quantum) (N : Nat) :
    CWriteRef (batch base N) (.bits (residueSamplingBits N)) :=
  finishWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)

/-- The complete parameter includes the unit, early-factor flag, and factor payload. -/
def batchParameter (base : RuntimeCtx .quantum) (N : Nat) :
    CWriteRef (batch base N) (ParameterShape N) :=
  finishWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)

/-- Each member writes its paid packing result to its own retained destination. -/
def batchPacked (base : RuntimeCtx .quantum) (N : Nat) (member : Fin membersPerBatch) :
    CWriteRef (batch base N) (.bits (measurementBits N)) :=
  (RuntimeResults.reference (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sampled base N) membersPerBatch member).underRetained (outcomes base N).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh

/-- The batch's recovery writes into a separate real optional-factor cell. -/
def batchFactor (base : RuntimeCtx .quantum) (N : Nat) :
    CWriteRef (batch base N) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead (outcomes base N) (outcomes base N).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh

/-- The complete classical frame contains the batches in their execution order. -/
def batches (N : Nat) : RuntimeCtx .quantum → Nat → RuntimeCtx .quantum
  | base, 0 => base
  | base, count + 1 => batches N (batch base N) count

/-- An existing writable cell crosses every later preallocated batch. -/
def batchesWrite (N : Nat) {shape : CShape} : {base : RuntimeCtx .quantum} →
    CWriteRef base shape → (count : Nat) → CWriteRef (batches N base count) shape
  | _, ref, 0 => ref
  | _, ref, count + 1 => batchesWrite N (batchWrite N ref) count

/-- An existing structural input crosses every later preallocated batch. -/
def batchesInput (N : Nat) {shape : CShape} : {base : RuntimeCtx .quantum} →
    CInputRef base shape → (count : Nat) → CInputRef (batches N base count) shape
  | _, input, 0 => input
  | _, input, count + 1 => batchesInput N (batchInput N input) count

/-- The final first-success destination is allocated after all batch destinations. -/
def context (base : RuntimeCtx .quantum) (N count : Nat) : RuntimeCtx .quantum :=
  (batches N base count).addRetained (batches N base count).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh

/-- The zero-count frame has only the old empty-result branch's classical output shape. -/
lemma rsaRecyclingFrame_context_zero (base : RuntimeCtx .quantum) (N : Nat) :
    context base N 0 = base.addRetained base.canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh := rfl

/-- Lift one batch-frame reference below the final selected-factor destination. -/
def finish {base : RuntimeCtx .quantum} {shape : CShape} (N count : Nat)
    (ref : CWriteRef (batches N base count) shape) : CWriteRef (context base N count) shape :=
  ref.underRetained (batches N base count).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh

/-- Each batch's source sample remains present in chronological batch order. -/
def samples (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → CWriteRef (batches N base count) (.bits (residueSamplingBits N))
  | _, 0, index => Fin.elim0 index
  | base, count + 1, index => Fin.cases
      (batchesWrite N (batchSample base N) count) (samples N (batch base N) count) index

/-- Each complete source parameter remains present in chronological batch order. -/
def parameters (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → CWriteRef (batches N base count) (ParameterShape N)
  | _, 0, index => Fin.elim0 index
  | base, count + 1, index => Fin.cases
      (batchesWrite N (batchParameter base N) count) (parameters N (batch base N) count) index

/-- All configured members of every batch have distinct retained packed destinations. -/
def packed (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → Fin membersPerBatch → CWriteRef (batches N base count) (.bits (measurementBits N))
  | _, 0, index, _ => Fin.elim0 index
  | base, count + 1, index, member => Fin.cases
      (batchesWrite N (batchPacked base N member) count)
      (fun previous => packed N (batch base N) count previous member) index

/-- Recovery factor destinations remain present in chronological batch order. -/
def factors (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Fin count → CWriteRef (batches N base count) (LatticeBatchRecoveryOutput.OutputShape N)
  | _, 0, index => Fin.elim0 index
  | base, count + 1, index => Fin.cases
      (batchesWrite N (batchFactor base N) count) (factors N (batch base N) count) index

/-- A batch source remains writable below the final selected-factor cell. -/
def sampleRef (base : RuntimeCtx .quantum) (N count : Nat) (index : Fin count) :
    CWriteRef (context base N count) (.bits (residueSamplingBits N)) :=
  finish N count (samples N base count index)

/-- A complete batch parameter remains writable in the single parent frame. -/
def parameterRef (base : RuntimeCtx .quantum) (N count : Nat) (index : Fin count) :
    CWriteRef (context base N count) (ParameterShape N) :=
  finish N count (parameters N base count index)

/-- The paid packing destination for one chronological batch member. -/
def packedRef (base : RuntimeCtx .quantum) (N count : Nat) (index : Fin count) (member : Fin
  membersPerBatch) :
    CWriteRef (context base N count) (.bits (measurementBits N)) :=
  finish N count (packed N base count index member)

/-- The independent recovery factor destination for one batch. -/
def factorRef (base : RuntimeCtx .quantum) (N count : Nat) (index : Fin count) :
    CWriteRef (context base N count) (LatticeBatchRecoveryOutput.OutputShape N) :=
  finish N count (factors N base count index)

/-- This is the only final selected-factor destination. -/
def selectedRef (base : RuntimeCtx .quantum) (N count : Nat) :
    CWriteRef (context base N count) (LatticeBatchRecoveryOutput.OutputShape N) :=
  .retainedHead (batches N base count) (batches N base count).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh

/-- Every original writable reference survives all preallocations with its role. -/
def liftWrite {base : RuntimeCtx .quantum} {shape : CShape} (N count : Nat)
    (ref : CWriteRef base shape) : CWriteRef (context base N count) shape :=
  finish N count (batchesWrite N ref count)

/-- Every original structural input survives all preallocations without a copy. -/
def liftInput {base : RuntimeCtx .quantum} {shape : CShape} (N count : Nat)
    (input : CInputRef base shape) : CInputRef (context base N count) shape :=
  (batchesInput N input count).underRetained (batches N base count).canonicalFreshKey
    (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh

/-- Each preallocated batch adds only classical cells, never a physical quantum wire. -/
lemma rsaRecyclingFrame_batch_wires (base : RuntimeCtx .quantum) (N : Nat) :
    (batch base N).quantumWires = base.quantumWires := by
  rw [batch, RuntimeCtx.quantumWires_addRetained]
  exact (RuntimeResults.shortDLP_runtimeResults_wires
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch).trans
      (by
        simp only [sampled, ShorStyle.Canonical.Sampler.Retained.context,
          ShorStyle.Canonical.Sampler.Retained.sampleContext,
          RuntimeCtx.quantumWires_addRetained])

lemma rsaRecyclingFrame_batches_wires (N : Nat) (base : RuntimeCtx .quantum) (count : Nat) :
    (batches N base count).quantumWires = base.quantumWires := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => exact (ih (batch base N)).trans (rsaRecyclingFrame_batch_wires base N)

lemma rsaRecyclingFrame_context_wires (base : RuntimeCtx .quantum) (N count : Nat) :
    (context base N count).quantumWires = base.quantumWires := by
  rw [context, RuntimeCtx.quantumWires_addRetained]
  exact rsaRecyclingFrame_batches_wires N base count

/-- A quantum-free caller gives one fixed quantum-free parent for the sole bank allocation. -/
lemma frameNoQuantum (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N count : Nat) : (context base N count).quantumWires = [] :=
  (rsaRecyclingFrame_context_wires base N count).trans noQuantum

omit configuration in
/-- One batch's source lift keeps the original underlying storage key. -/
lemma rsaRecyclingFrame_sampledWrite_key {base : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (ref : CWriteRef base shape) : (sampledWrite N ref).key = ref.key := rfl

omit configuration in
private lemma retainedWrite_key {ctx : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef ctx shape) (key : StorageKey) (retainedShape : CShape)
    (fresh : key ∉ ctx.keys) :
    (ref.underRetained key retainedShape fresh).key = ref.key := rfl

/-- Subsequent packed and factor destinations keep every earlier source identity. -/
lemma rsaRecyclingFrame_finishWrite_key {base : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (ref : CWriteRef (sampled base N) shape) :
    (finishWrite N ref).key = ref.key :=
  (retainedWrite_key (ctx := outcomes base N)
    (RuntimeResults.liftWrite (shortLogBits N) (tradeoffBits N) (arithmeticBits N) ref
      membersPerBatch)
    (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    (outcomes base N).canonicalFreshKey_fresh).trans
      (RuntimeResults.shortDLP_runtimeResults_liftWrite_key
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) ref membersPerBatch)

/-- Extending by a complete classical batch preserves an older writable cell's key. -/
lemma rsaRecyclingFrame_batchWrite_key {base : RuntimeCtx .quantum} {shape : CShape}
    (N : Nat) (ref : CWriteRef base shape) : (batchWrite N ref).key = ref.key :=
  (rsaRecyclingFrame_finishWrite_key N _).trans (rsaRecyclingFrame_sampledWrite_key N ref)

/-- All batch preallocations preserve an older writable cell's physical key. -/
lemma rsaRecyclingFrame_batchesWrite_key (N : Nat) {base : RuntimeCtx .quantum}
    {shape : CShape} (ref : CWriteRef base shape) (count : Nat) :
    (batchesWrite N ref count).key = ref.key := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih => exact (ih (batchWrite N ref)).trans (rsaRecyclingFrame_batchWrite_key N ref)

/-- The final selection destination changes no existing caller storage identity. -/
lemma rsaRecyclingFrame_liftWrite_key (N count : Nat) {base : RuntimeCtx .quantum}
    {shape : CShape} (ref : CWriteRef base shape) : (liftWrite N count ref).key = ref.key :=
  rsaRecyclingFrame_batchesWrite_key N ref count

omit configuration in
private lemma reference_mem {base : RuntimeCtx .quantum} {shape : CShape}
    (ref : CWriteRef base shape) : ref.key ∈ base.keys :=
  CInputRef.storageKeys_subset_context (.storage ref.toCStorageRef) (List.mem_singleton_self _)

omit configuration in
private lemma outcome_keys_include (m ell width : Nat) (base : RuntimeCtx .quantum)
    (count : Nat) {key : StorageKey} (present : key ∈ base.keys) :
    key ∈ (RuntimeResults.context m ell width base count).keys := by
  induction count generalizing base with
  | zero => exact present
  | succ count ih =>
      exact ih (RuntimeResults.next m ell width base) (List.mem_cons_of_mem _ present)

private lemma batch_keys_include (base : RuntimeCtx .quantum) (N : Nat)
    {key : StorageKey} (present : key ∈ base.keys) : key ∈ (batch base N).keys :=
  List.mem_cons_of_mem _ (outcome_keys_include (shortLogBits N) (tradeoffBits N)
    (arithmeticBits N) (sampled base N) membersPerBatch
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)))

private lemma batchPacked_key (base : RuntimeCtx .quantum) (N : Nat) (member : Fin
  membersPerBatch) :
    (batchPacked base N member).key =
      (RuntimeResults.reference (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
        (sampled base N) membersPerBatch member).key :=
  retainedWrite_key (ctx := outcomes base N)
    (RuntimeResults.reference (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (sampled base N) membersPerBatch member)
    (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    (outcomes base N).canonicalFreshKey_fresh

private lemma batch_packed_fresh (base : RuntimeCtx .quantum) (N : Nat) (member : Fin
  membersPerBatch) :
    (batchPacked base N member).key ∉ base.keys := by
  rw [batchPacked_key]
  intro present
  exact RuntimeResults.shortDLP_runtimeResults_reference_fresh
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch member
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present))

private lemma batch_packed_injective (base : RuntimeCtx .quantum) (N : Nat) :
    Function.Injective (fun member => (batchPacked base N member).key) := by
  intro left right same
  exact RuntimeResults.shortDLP_runtimeResults_reference_injective
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch
      ((batchPacked_key base N left).symm.trans (same.trans (batchPacked_key base N right)))

private lemma packed_fresh (N : Nat) (base : RuntimeCtx .quantum) (count : Nat)
    (index : Fin count) (member : Fin membersPerBatch) :
    (packed N base count index member).key ∉ base.keys := by
  induction count generalizing base with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · change (batchesWrite N (batchPacked base N member) count).key ∉ base.keys
        rw [rsaRecyclingFrame_batchesWrite_key]
        exact batch_packed_fresh base N member
      · intro present
        exact ih (batch base N) index (batch_keys_include base N present)

/-- The actual membersPerBatch*k packed cells have pairwise distinct underlying storage keys. -/
lemma rsaRecyclingFrame_packed_distinct (N : Nat) (base : RuntimeCtx .quantum) (count : Nat) :
    Function.Injective (fun address : Fin count × Fin membersPerBatch =>
      (packed N base count address.1 address.2).key) := by
  induction count generalizing base with
  | zero => intro address; exact Fin.elim0 address.1
  | succ count ih =>
      rintro ⟨left, member⟩ ⟨right, other⟩
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          have memberSame := batch_packed_injective base N
            ((rsaRecyclingFrame_batchesWrite_key N (batchPacked base N member) count).symm.trans
              (same.trans (rsaRecyclingFrame_batchesWrite_key N (batchPacked base N other) count)))
          cases memberSame
          rfl
        · intro same
          apply False.elim
          apply packed_fresh N (batch base N) count right other
          have keySame : (packed N (batch base N) count right other).key =
              (batchPacked base N member).key :=
            same.symm.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchPacked base N member)
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          apply False.elim
          apply packed_fresh N (batch base N) count left member
          have keySame : (packed N (batch base N) count left member).key =
              (batchPacked base N other).key :=
            same.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchPacked base N other)
        · intro same
          change (packed N (batch base N) count left member).key =
            (packed N (batch base N) count right other).key at same
          have pairSame : (left, member) = (right, other) := ih (batch base N) same
          exact congrArg (fun address : Fin count × Fin membersPerBatch => (address.1.succ,
            address.2)) pairSame

/-- Final selection and later quantum preparation preserve packed-cell separation. -/
lemma rsaRecyclingFrame_packedRef_distinct (base : RuntimeCtx .quantum) (N count : Nat) :
    Function.Injective (fun address : Fin count × Fin membersPerBatch =>
      (packedRef base N count address.1 address.2).key) :=
  rsaRecyclingFrame_packed_distinct N base count

/-- Paid packed destinations cannot overwrite any caller input cell. -/
lemma rsaRecyclingFrame_packedRef_fresh (base : RuntimeCtx .quantum) (N count : Nat)
    (index : Fin count) (member : Fin membersPerBatch) :
    (packedRef base N count index member).key ∉ base.keys :=
  packed_fresh N base count index member

/-- The final selected factor is separate from every previously allocated batch cell. -/
lemma rsaRecyclingFrame_selected_separate (base : RuntimeCtx .quantum) (N count : Nat)
    {shape : CShape} (ref : CWriteRef (batches N base count) shape) :
    (selectedRef base N count).key ≠ (finish N count ref).key := by
  intro same
  change (batches N base count).canonicalFreshKey = ref.key at same
  exact (batches N base count).canonicalFreshKey_fresh (same.symm ▸ reference_mem ref)

/-- No packed outcome can overwrite any complete source parameter from any batch. -/
lemma rsaRecyclingFrame_packed_parameter_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) (member : Fin membersPerBatch) :
    (packedRef base N count index member).key ≠ (parameterRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (packedRef base N count index member).toCStorageRef
    (parameterRef base N count previous).toCStorageRef same
  cases shapes

/-- No paid packed destination can alias any batch's optional-factor cell. -/
lemma rsaRecyclingFrame_packed_factor_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) (member : Fin membersPerBatch) :
    (packedRef base N count index member).key ≠ (factorRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (packedRef base N count index member).toCStorageRef
    (factorRef base N count previous).toCStorageRef same
  cases shapes

omit configuration in
private lemma sample_width_ne_measurement (N : Nat) :
    residueSamplingBits N ≠ measurementBits N := by
  have short := shortLogBits_le_modulusBits_add_one N
  have tradeoff := tradeoffBits_le_modulusBits_add_one N
  have positive := measurementBits_pos N
  unfold measurementBits at positive ⊢
  simp only [residueSamplingBits, ShorStyle.Canonical.residueSamplingBits,
    ShorStyle.Canonical.residueProposalCount]
  change 16 * modulusBits N ≠ _
  omega

/-- A paid packed observation cannot overwrite any batch's retained random source sample. -/
lemma rsaRecyclingFrame_packed_sample_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) (member : Fin membersPerBatch) :
    (packedRef base N count index member).key ≠ (sampleRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (packedRef base N count index member).toCStorageRef
    (sampleRef base N count previous).toCStorageRef same
  exact sample_width_ne_measurement N (CShape.bits.inj shapes).symm

private lemma factor_fresh (N : Nat) (base : RuntimeCtx .quantum) (count : Nat)
    (index : Fin count) : (factors N base count index).key ∉ base.keys := by
  induction count generalizing base with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · change (batchesWrite N (batchFactor base N) count).key ∉ base.keys
        rw [rsaRecyclingFrame_batchesWrite_key]
        intro present
        exact (outcomes base N).canonicalFreshKey_fresh
          (outcome_keys_include (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
            (sampled base N) membersPerBatch
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ present)))
      · intro present
        exact ih (batch base N) index (batch_keys_include base N present)

/-- Different batches write recovery into different underlying optional-factor cells. -/
lemma rsaRecyclingFrame_factorRef_distinct (N : Nat) (base : RuntimeCtx .quantum)
    (count : Nat) : Function.Injective (fun index => (factorRef base N count index).key) := by
  induction count generalizing base with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          apply False.elim
          apply factor_fresh N (batch base N) count right
          have keySame : (factors N (batch base N) count right).key = (batchFactor base N).key :=
            same.symm.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchFactor base N)
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          apply False.elim
          apply factor_fresh N (batch base N) count left
          have keySame : (factors N (batch base N) count left).key = (batchFactor base N).key :=
            same.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchFactor base N)
        · intro same
          exact congrArg Fin.succ (ih (batch base N) same)

private lemma batchSample_key (base : RuntimeCtx .quantum) (N : Nat) :
    (batchSample base N).key = base.canonicalFreshKey := by
  have preserved := rsaRecyclingFrame_finishWrite_key (base := base) N
    (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)
  exact preserved.trans rfl

private lemma batchParameter_key (base : RuntimeCtx .quantum) (N : Nat) :
    (batchParameter base N).key =
      (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey := by
  have preserved := rsaRecyclingFrame_finishWrite_key (base := base) N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)
  exact preserved.trans rfl

private lemma sample_fresh (N : Nat) (base : RuntimeCtx .quantum) (count : Nat)
    (index : Fin count) : (samples N base count index).key ∉ base.keys := by
  induction count generalizing base with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · change (batchesWrite N (batchSample base N) count).key ∉ base.keys
        rw [rsaRecyclingFrame_batchesWrite_key, batchSample_key]
        exact base.canonicalFreshKey_fresh
      · intro present
        exact ih (batch base N) index (batch_keys_include base N present)

/-- Every batch's retained sample has its own underlying physical storage key. -/
lemma rsaRecyclingFrame_sampleRef_distinct (N : Nat) (base : RuntimeCtx .quantum)
    (count : Nat) : Function.Injective (fun index => (sampleRef base N count index).key) := by
  induction count generalizing base with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          apply False.elim
          apply sample_fresh N (batch base N) count right
          have keySame : (samples N (batch base N) count right).key = (batchSample base N).key :=
            same.symm.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchSample base N)
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          apply False.elim
          apply sample_fresh N (batch base N) count left
          have keySame : (samples N (batch base N) count left).key = (batchSample base N).key :=
            same.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchSample base N)
        · intro same
          exact congrArg Fin.succ (ih (batch base N) same)

private lemma parameter_fresh (N : Nat) (base : RuntimeCtx .quantum) (count : Nat)
    (index : Fin count) : (parameters N base count index).key ∉ base.keys := by
  induction count generalizing base with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · change (batchesWrite N (batchParameter base N) count).key ∉ base.keys
        rw [rsaRecyclingFrame_batchesWrite_key, batchParameter_key]
        intro present
        exact (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey_fresh
          (List.mem_cons_of_mem _ present)
      · intro present
        exact ih (batch base N) index (batch_keys_include base N present)

/-- Every batch's retained parameter has its own underlying physical storage key. -/
lemma rsaRecyclingFrame_parameterRef_distinct (N : Nat) (base : RuntimeCtx .quantum)
    (count : Nat) : Function.Injective (fun index => (parameterRef base N count index).key) := by
  induction count generalizing base with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          apply False.elim
          apply parameter_fresh N (batch base N) count right
          have keySame : (parameters N (batch base N) count right).key =
              (batchParameter base N).key :=
            same.symm.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchParameter base N)
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          apply False.elim
          apply parameter_fresh N (batch base N) count left
          have keySame : (parameters N (batch base N) count left).key =
              (batchParameter base N).key :=
            same.trans (rsaRecyclingFrame_batchesWrite_key N _ count)
          exact keySame.symm ▸ reference_mem (batchParameter base N)
        · intro same
          exact congrArg Fin.succ (ih (batch base N) same)

/-- Retained sample and parameter destinations are separate in every pair of batches. -/
lemma rsaRecyclingFrame_sample_parameter_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) :
    (sampleRef base N count index).key ≠
      (parameterRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (sampleRef base N count index).toCStorageRef
    (parameterRef base N count previous).toCStorageRef same
  cases shapes

/-- Retained sample and factor destinations have separate actual keys in every pair of batches. -/
lemma rsaRecyclingFrame_sample_factor_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) :
    (sampleRef base N count index).key ≠ (factorRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (sampleRef base N count index).toCStorageRef
    (factorRef base N count previous).toCStorageRef same
  cases shapes

/-- Retained parameter and factor destinations are separate in every pair of batches. -/
lemma rsaRecyclingFrame_parameter_factor_separate (base : RuntimeCtx .quantum) (N count : Nat)
    (index previous : Fin count) :
    (parameterRef base N count index).key ≠ (factorRef base N count previous).key := by
  intro same
  have shapes := CStorageRef.storageRef_shape_eq_of_key
    (parameterRef base N count index).toCStorageRef
    (factorRef base N count previous).toCStorageRef same
  cases shapes

end

end QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame
