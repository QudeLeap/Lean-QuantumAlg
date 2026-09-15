/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Frame
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Reuse.Probability

/-!
# Actual recovered factors jointly with earlier caller values

The same fixed bank supplies its real source, parameter and sixteen samples.
On every positive source block the original parameter condition follows from
that actual source law. The original recovery record writes the factor and
preserves the earlier observation. Complete reference weights therefore have
the original recovery kernel jointly with that observation, for both the
first preparation and the later redraw and paid reuse. No normalization,
independent sampler or successful-recovery premise is supplied by a caller.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Batch.context Batch.code Batch.nextBatch into step
  NativeBatchRecovery.packedValue

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem source_support {origin : RuntimeCtx .quantum}
    (input : Input N) {Reference : Register} {History FinalHistory : Type}
    [Fintype History] [Fintype FinalHistory]
    (initial : State origin Reference History)
    (final : State (Batch.context base noQuantum N) Reference FinalHistory)
    (sampled : ∀ (weight : (NativeBatch.resultShape N).Value → ℂ) left right,
      ExecutionState.referenceFiberSum final
        (fun entry _ => weight (entry.1.read (Batch.sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum initial
        (fun _ _ => ∑ value : (NativeBatch.resultShape N).Value,
          ((NativeBatch.sourceDistribution input value).toReal : ℂ) * weight value) left right)
    (entry : Store (Batch.context base noQuantum N) × FinalHistory)
    (positive : 0 < (final.block entry).mass) :
    entry.1.read (Batch.sourceRead base noQuantum N) ∈
      (NativeBatch.sourceDistribution input).support := by
  apply NativeBatchReuseRecovery.read_mem_support_of_reference initial final
    (fun record => record.1.read (Batch.sourceRead base noQuantum N))
    (NativeBatch.sourceDistribution input) ?_ entry positive
  intro selected left right
  exact (sampled (fun value => if value = selected then 1 else 0) left right).trans
    (congrArg (fun scalar : ℂ =>
      ExecutionState.referenceFiberSum initial (fun _ _ => scalar) left right)
      (PMF.sum_toReal_indicator (NativeBatch.sourceDistribution input) selected))

private theorem recovered_on_support (input : Input N)
    (store : Store (Batch.context base noQuantum N))
    (supported : store.read (Batch.sourceRead base noQuantum N) ∈
      (NativeBatch.sourceDistribution input).support) :
    (step base noQuantum N input store).1.read
      (.storage (Batch.factorRef base noQuantum N).toCStorageRef) =
        NativeBatchRecovery.packedValue (store.read (Batch.sourceRead base noQuantum N)) :=
  (nativeOracle_batchRecovery_value base noQuantum N input
    (NativeBatchRecovery.decodeSource (store.read (Batch.sourceRead base noQuantum N))) store
    (NativeBatchRecovery.sourceDistribution_parameter input _ supported)).trans
      (packed_read base noQuantum N store).symm

private theorem into_reference (input : Input N)
    {shape : CShape} (observed : CInputRef (Batch.context base noQuantum N) shape)
    (factorFree : (Batch.factorRef base noQuantum N).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History)
    (supported : ∀ entry, 0 < (state.block entry).mass →
      entry.1.read (Batch.sourceRead base noQuantum N) ∈
        (NativeBatch.sourceDistribution input).support)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((into base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read observed)
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read observed)
          (NativeBatchRecovery.packedValue
            (entry.1.read (Batch.sourceRead base noQuantum N)))) left right := by
  let update := fun entry : Store (Batch.context base noQuantum N) × History =>
    ((step base noQuantum N input entry.1).1,
      (entry.2, (step base noQuantum N input entry.1).2))
  let observe := fun entry : Store (Batch.context base noQuantum N) ×
      (History × (into base noQuantum N input).Path) =>
    weight (entry.1.read observed)
      (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (Batch.context base noQuantum N) Reference
        (History × (into base noQuantum N input).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry) left right)
    (nativeOracle_batchRecovery_execute base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry) left right).trans ?_)
  apply NativeBatchReuseRecovery.reference_eq_on_support
  intro entry positive basis
  dsimp only [observe, update]
  exact congrArg₂ weight
    (nativeOracle_batchRecovery_frame base noQuantum N input entry.1 observed factorFree)
    (recovered_on_support base noQuantum N input entry.1 (supported entry positive))

private theorem recovered_moment (input : Input N)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ) :
    (∑ value : (NativeBatch.resultShape N).Value,
      ((NativeBatch.sourceDistribution input value).toReal : ℂ) *
        weight (NativeBatchRecovery.packedValue value)) =
      ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
        ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
          factor).toReal : ℂ) * weight factor := by
  have mapped := (PMF.sum_map_toReal_mul (NativeBatch.sourceDistribution input)
    NativeBatchRecovery.packedValue weight).symm
  rw [NativeBatchRecovery.sourceDistribution_map_packedValue input] at mapped
  exact mapped

/-- The real first batch and recovery preserve the original factor law jointly with the caller. -/
theorem nativeOracle_batchRecovery_first_frame_reference (input : Input N)
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((first base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read (Batch.callerInput base noQuantum N observed))
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight (entry.1.read observed) factor) left right := by
  let sourceState := (Batch.code base noQuantum N input).execute Reference state
  have supported := source_support base noQuantum N input state sourceState
    (Batch.nativeOracle_batch_source_weighted_reference base noQuantum N input state)
  have recovered := into_reference base noQuantum N input
    (Batch.callerInput base noQuantum N observed)
    (Batch.nativeOracle_batch_caller_factor_separate base noQuantum N observed)
    sourceState supported weight left right
  have sampled := Batch.nativeOracle_batch_first_source_frame_reference base noQuantum N input
    observed state (fun old value => weight old (NativeBatchRecovery.packedValue value)) left right
  have mapped := congrArg
    (fun observe : Store base → ℂ => ExecutionState.referenceFiberSum state
      (fun entry _ => observe entry.1) left right)
    (funext fun store => recovered_moment N input (weight (store.read observed)))
  exact (Circuit.referenceFiberSum_execute_seq (Batch.code base noQuantum N input)
    (into base noQuantum N input) state
    (fun store => weight (store.read (Batch.callerInput base noQuantum N observed))
      (store.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) left right).trans
      (recovered.trans (sampled.trans mapped))

/-- Actual redraw, paid reuse and recovery have the same factor kernel with protected old values. -/
theorem nativeOracle_batchRecovery_next_frame_reference (input : Input N)
    {shape : CShape} (observed : CInputRef (Batch.context base noQuantum N) shape)
    (separated : Batch.FrameSeparated base noQuantum N observed)
    (factorFree : (Batch.factorRef base noQuantum N).key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((next base noQuantum N input).execute Reference state)
      (fun entry _ => weight (entry.1.read observed)
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight (entry.1.read observed) factor) left right := by
  let sourceState := (Batch.nextBatch base noQuantum N input).execute Reference state
  have supported := source_support base noQuantum N input state sourceState
    (Batch.nativeOracle_batch_next_source_weighted_reference base noQuantum N input state)
  have recovered := into_reference base noQuantum N input observed factorFree
    sourceState supported weight left right
  have sampled := Batch.nativeOracle_batch_next_source_frame_reference base noQuantum N input
    observed separated state (fun old value => weight old (NativeBatchRecovery.packedValue value))
    left right
  have mapped := congrArg
    (fun observe : Store (Batch.context base noQuantum N) → ℂ =>
      ExecutionState.referenceFiberSum state (fun entry _ => observe entry.1) left right)
    (funext fun store => recovered_moment N input (weight (store.read observed)))
  exact (Circuit.referenceFiberSum_execute_seq (Batch.nextBatch base noQuantum N input)
    (into base noQuantum N input) state
    (fun store => weight (store.read observed)
      (store.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) left right).trans
      (recovered.trans (sampled.trans mapped))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery
