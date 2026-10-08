/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Reference

/-!
# Complete physical EH recovery with an original caller read

The actual classical recovery consumes the source, parameter and sixteen
sample cells of one paid batch. Its factor output retains the original
caller value and its correlation with every external reference block.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private theorem recovered_caller_reference
    {origin : RuntimeCtx .quantum}
    (sampler : Circuit (model input) origin (Batch.context base noQuantum N))
    {shape : CShape} (original : CInputRef origin shape)
    (retained : CInputRef (Batch.context base noQuantum N) shape)
    (factorFree : (Batch.factorRef base noQuantum N).key ∉ retained.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (sourceLaw : (((sampler.execute Reference state).toPMF
      ((sampler.execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read (Batch.sourceRead base noQuantum N))) =
      Batch.sourceDistribution input)
    (jointLaw : ∀ (jointWeight : shape.Value → (Batch.resultShape N).Value → ℂ)
      (left right : Reference.Index),
      ExecutionState.referenceFiberSum (sampler.execute Reference state)
        (fun entry _ => jointWeight (entry.1.read retained)
          (entry.1.read (Batch.sourceRead base noQuantum N))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ output : (Batch.resultShape N).Value,
          ((Batch.sourceDistribution input output).toReal : ℂ) *
            jointWeight (entry.1.read original) output) left right)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((sampler.seq (into base noQuantum N input)).execute Reference state)
      (fun entry _ => weight (entry.1.read retained)
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (entry.1.read original) (Batch.SourceRecovery.packedValue output))
      left right := by
  let before := sampler.execute Reference state
  have normalizedBefore := (sampler.execute_mass Reference state).trans normalized
  have recovered := into_joint_read base noQuantum N input retained factorFree
    before normalizedBefore sourceLaw
  have mapped := congrArg
    (fun result : ExecutionState
        (shape.Value × (LatticeBatchRecoveryOutput.OutputShape N).Value)
        (Register.prod (Batch.context base noQuantum N).register Reference) =>
      ExecutionState.referenceFiberSum result
        (fun entry _ => weight entry.1 entry.2) left right) recovered
  have recoveryLaw :
      ExecutionState.referenceFiberSum
        ((into base noQuantum N input).execute Reference before)
        (fun entry _ => weight (entry.1.read retained)
          (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
        left right =
      ExecutionState.referenceFiberSum before
        (fun entry _ => weight (entry.1.read retained)
          (Batch.SourceRecovery.packedValue
            (entry.1.read (Batch.sourceRead base noQuantum N))))
        left right := by
    simpa only [ExecutionState.referenceFiberSum_mapClassical] using mapped
  exact (Circuit.referenceFiberSum_execute_seq sampler (into base noQuantum N input)
    state (fun store => weight (store.read retained)
      (store.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
    left right).trans (recoveryLaw.trans
      (jointLaw (fun old source => weight old (Batch.SourceRecovery.packedValue source))
        left right))

/-- The first paid batch and recovery retain the original caller value jointly
with the optional factor in every reference matrix entry. -/
theorem run_caller_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((run base noQuantum N input).code.execute Reference state)
      (fun entry _ => weight
        (entry.1.read (Batch.callerInput base noQuantum N observed))
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (entry.1.read observed) (Batch.SourceRecovery.packedValue output))
      left right := by
  exact recovered_caller_reference base noQuantum N input
    (Batch.code base noQuantum N input) observed
    (Batch.callerInput base noQuantum N observed)
    (Batch.caller_factor_separated base noQuantum N observed)
    state normalized (Batch.source_toPMF base noQuantum N input state normalized)
    (Batch.source_caller_weighted_reference base noQuantum N input observed state)
    weight left right

/-- Every later redraw, paid reuse and recovery retains the original caller
value jointly with the new optional factor and external reference. -/
theorem nextRun_caller_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference
      ((model input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : shape.Value → (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextRun base noQuantum N input).code.execute Reference state)
      (fun entry _ => weight
        (entry.1.read (Batch.callerInput base noQuantum N observed))
        (entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
      left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ output : (Batch.resultShape N).Value,
        ((Batch.sourceDistribution input output).toReal : ℂ) *
          weight (entry.1.read (Batch.callerInput base noQuantum N observed))
            (Batch.SourceRecovery.packedValue output))
      left right := by
  exact recovered_caller_reference base noQuantum N input
    (Batch.nextBatch base noQuantum N input)
    (Batch.callerInput base noQuantum N observed)
    (Batch.callerInput base noQuantum N observed)
    (Batch.caller_factor_separated base noQuantum N observed)
    state normalized (Batch.next_source_toPMF base noQuantum N input state normalized)
    (Batch.next_source_caller_weighted_reference base noQuantum N input observed state)
    weight left right

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery
