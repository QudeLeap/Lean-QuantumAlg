/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Source.Recovery
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Complete actual recovery of a declared EH batch

The paid classical recovery reads the exact retained source, parameter and
sixteen sample cells of the declared physical program. On the support of the
proved joint source law, it writes the corresponding pure complete recovery
value to the actual factor cell without changing external-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Batch.context into step

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

variable {environment : (model N).Environment}

lemma packed_read (store : Store (Batch.context base noQuantum N)) :
    SourceRecovery.packedValue (store.read (Batch.sourceRead base noQuantum N)) =
      LatticeFixedBatchRecoveryMachine.batchValue
        (SourceRecovery.decodeSource (store.read (Batch.sourceRead base noQuantum N)))
        (terminals base noQuantum N) store := by
  unfold SourceRecovery.packedValue SourceRecovery.recoverValue
    LatticeFixedBatchRecoveryMachine.batchValue
  apply congrArg (LatticeBatchRecoveryOutput.outputValue (N := N))
  apply congrArg (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N))
  apply List.Vector.ext
  intro index
  simp only [SourceRecovery.decodeSamples, SourceRecovery.decodeOutcomes,
    LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map, List.Vector.get_ofFn]
  congr 1

lemma sampled_parameter
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History)
    (normalized : state.IsNormalized)
    (sourceLaw : (state.toPMF normalized).map
      (fun entry => entry.1.read (Batch.sourceRead base noQuantum N)) =
        Batch.sourceDistribution input)
    (entry : Store (Batch.context base noQuantum N) × History)
    (positive : 0 < (state.block entry).mass) :
    entry.1.read (parameter base noQuantum N) =
      parameterValue input
        (SourceRecovery.decodeSource (entry.1.read (Batch.sourceRead base noQuantum N))) := by
  have supported := (ExecutionState.mem_support_toPMF_iff state normalized entry).mpr positive
  have observed : entry.1.read (Batch.sourceRead base noQuantum N) ∈
      (Batch.sourceDistribution input).support := by
    rw [← sourceLaw, PMF.mem_support_map_iff]
    exact ⟨entry, supported, rfl⟩
  exact SourceRecovery.sourceDistribution_parameter input _ observed

/-- The real allocated recovery maps every positive source block to its
pure complete first-success factor value in the same reference matrix. -/
lemma into_factor_read
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (sourceLaw : (state.toPMF normalized).map
      (fun entry => entry.1.read (Batch.sourceRead base noQuantum N)) =
        Batch.sourceDistribution input) :
    ((into base noQuantum N input).execute environment Reference state).mapClassical
      (fun entry => entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)) =
    state.mapClassical (fun entry =>
      SourceRecovery.packedValue (entry.1.read (Batch.sourceRead base noQuantum N))) := by
  have executed := congrArg
    (fun output : State (Batch.context base noQuantum N) Reference
        ((model N).HiddenState × (History × (into base noQuantum N input).Path)) =>
      output.mapClassical (fun entry =>
        entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
    (into_execute (environment := environment) base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.executionState_mapClassical_comp state
    (fun entry =>
      (let actual := step base noQuantum N input entry.1
       (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (fun entry => entry.1.read
      (.storage (Batch.factorRef base noQuantum N).toCStorageRef))).trans ?_)
  apply ExecutionState.mapClassical_eq_of_support
  intro entry positive
  exact (value base noQuantum N input
    (SourceRecovery.decodeSource (entry.1.read (Batch.sourceRead base noQuantum N)))
    entry.1
    (sampled_parameter base noQuantum N input state normalized sourceLaw entry positive)).trans
      (packed_read base noQuantum N entry.1).symm

set_option maxRecDepth 2048

/-- Complete paid recovery preserves a protected caller read jointly with the
factor it writes, including its correlation with an external reference. -/
lemma into_joint_read
    {Reference : Register} {History : Type} [Fintype History]
    {shape : CShape} (observed : CInputRef (Batch.context base noQuantum N) shape)
    (factorFree : (Batch.factorRef base noQuantum N).key ∉ observed.storageKeys)
    (state : State (Batch.context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (normalized : state.IsNormalized)
    (sourceLaw : (state.toPMF normalized).map
      (fun entry => entry.1.read (Batch.sourceRead base noQuantum N)) =
        Batch.sourceDistribution input) :
    ((into base noQuantum N input).execute environment Reference state).mapClassical
      (fun entry => (entry.1.read observed,
        entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) =
    state.mapClassical (fun entry => (entry.1.read observed,
      SourceRecovery.packedValue (entry.1.read (Batch.sourceRead base noQuantum N)))) := by
  have executed := congrArg
    (fun output : State (Batch.context base noQuantum N) Reference
        ((model N).HiddenState × (History × (into base noQuantum N input).Path)) =>
      output.mapClassical (fun entry => (entry.1.read observed,
        entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))))
    (into_execute (environment := environment) base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.executionState_mapClassical_comp state
    (fun entry =>
      (let actual := step base noQuantum N input entry.1
       (actual.1, (entry.2.1, (entry.2.2, actual.2)))))
    (fun entry => (entry.1.read observed,
      entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))).trans ?_)
  apply ExecutionState.mapClassical_eq_of_support
  intro entry positive
  apply Prod.ext
  · exact (caller_frame base noQuantum N input entry.1) observed factorFree
  · change (step base noQuantum N input entry.1).1.read
        (.storage (Batch.factorRef base noQuantum N).toCStorageRef) =
        SourceRecovery.packedValue (entry.1.read (Batch.sourceRead base noQuantum N))
    exact (value base noQuantum N input
      (SourceRecovery.decodeSource (entry.1.read (Batch.sourceRead base noQuantum N)))
      entry.1
      (sampled_parameter base noQuantum N input state normalized sourceLaw entry positive)).trans
        (packed_read base noQuantum N entry.1).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch.Recovery
