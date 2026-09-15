/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Probability
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Original recovery probabilities from the actual original-width oracle bank

The actual joint source read supplies the parameter of its own decoded
residue on every positive execution block. The original deterministic
recovery therefore writes the pure recovery of those same sixteen samples.
Complete observed density operators agree before taking their traces, so
arbitrary external-reference correlations remain admissible. Both the first
run and later paid bank reuse yield the original optional factor law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Batch.context Batch.code Batch.nextBatch into step

private theorem observed_pmf_congr {C D Value : Type}
    [Fintype C] [Fintype D] [Fintype Value] {R : Register}
    (first : ExecutionState C R) (second : ExecutionState D R)
    (firstNormalized : first.IsNormalized) (secondNormalized : second.IsNormalized)
    (firstRead : C → Value) (secondRead : D → Value)
    (equal : first.mapClassical firstRead = second.mapClassical secondRead) :
    (first.toPMF firstNormalized).map firstRead =
      (second.toPMF secondNormalized).map secondRead := by
  have mapped : (first.mapClassical firstRead).toPMF
        (first.mapClassical_normalized firstNormalized firstRead) =
      (second.mapClassical secondRead).toPMF
        (second.mapClassical_normalized secondNormalized secondRead) := by
    apply PMF.ext
    intro value
    exact congrArg (fun state : ExecutionState Value R =>
      ENNReal.ofReal (state.block value).mass) equal
  exact (ExecutionState.toPMF_mapClassical first firstNormalized firstRead).symm.trans
    (mapped.trans (ExecutionState.toPMF_mapClassical second secondNormalized secondRead))

private theorem sequence_read {pre middle post : RuntimeCtx .quantum}
    (first : Circuit pre middle) (second : Circuit middle post)
    {Reference : Register} {History Value : Type} [Fintype History] [Fintype Value]
    (state : State pre Reference History) (read : Store post → Value) :
    ((first.seq second).execute Reference state).mapClassical (fun entry => read entry.1) =
      (second.execute Reference (first.execute Reference state)).mapClassical
        (fun entry => read entry.1) := by
  have executed := congrArg
    (fun output : State post Reference (History × (first.seq second).Path) =>
      output.mapClassical (fun entry => read entry.1))
    (Circuit.execute_seq first second state)
  refine executed.trans ?_
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]

private theorem map_law {A B C : Type} (distribution : PMF A)
    (observe : A → B) (recover : B → C) (source : PMF B) (result : PMF C)
    (first : distribution.map observe = source) (second : source.map recover = result) :
    distribution.map (recover ∘ observe) = result :=
  (PMF.map_comp observe distribution recover).symm.trans
    ((congrArg (fun probability : PMF B => probability.map recover) first).trans second)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem packed_read (store : Store (Batch.context base noQuantum N)) :
    NativeBatchRecovery.packedValue (store.read (Batch.sourceRead base noQuantum N)) =
      LatticeFixedBatchRecoveryMachine.batchValue
        (NativeBatchRecovery.decodeSource (store.read (Batch.sourceRead base noQuantum N)))
        (terminals base noQuantum N) store := by
  unfold NativeBatchRecovery.packedValue NativeBatchRecovery.recoverValue
    LatticeFixedBatchRecoveryMachine.batchValue
  apply congrArg (LatticeBatchRecoveryOutput.outputValue (N := N))
  apply congrArg (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N))
  apply List.Vector.ext
  intro index
  simp only [NativeBatchRecovery.decodeSamples, NativeBatchRecovery.decodeOutcomes,
    LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map, List.Vector.get_ofFn]
  congr 1

private theorem sampled_parameter (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History)
    (normalized : state.IsNormalized)
    (sourceLaw : (state.toPMF normalized).map
      (fun entry => entry.1.read (Batch.sourceRead base noQuantum N)) =
        NativeBatch.sourceDistribution input)
    (entry : Store (Batch.context base noQuantum N) × History)
    (positive : 0 < (state.block entry).mass) :
    entry.1.read (parameter base noQuantum N) =
      parameterValue input
        (NativeBatchRecovery.decodeSource (entry.1.read (Batch.sourceRead base noQuantum N))) := by
  have supported := (ExecutionState.mem_support_toPMF_iff state normalized entry).mpr positive
  have observed : entry.1.read (Batch.sourceRead base noQuantum N) ∈
      (NativeBatch.sourceDistribution input).support := by
    rw [← sourceLaw, PMF.mem_support_map_iff]
    exact ⟨entry, supported, rfl⟩
  exact NativeBatchRecovery.sourceDistribution_parameter input _ observed

private theorem recovery_read (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Batch.context base noQuantum N) Reference History)
    (normalized : state.IsNormalized)
    (sourceLaw : (state.toPMF normalized).map
      (fun entry => entry.1.read (Batch.sourceRead base noQuantum N)) =
        NativeBatch.sourceDistribution input) :
    ((into base noQuantum N input).execute Reference state).mapClassical
        (fun entry => entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)) =
      state.mapClassical (fun entry =>
        NativeBatchRecovery.packedValue (entry.1.read (Batch.sourceRead base noQuantum N))) := by
  have executed := congrArg
    (fun output : State (Batch.context base noQuantum N) Reference
        (History × (into base noQuantum N input).Path) =>
      output.mapClassical (fun entry =>
        entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef)))
    (nativeOracle_batchRecovery_execute base noQuantum N input Reference state)
  refine executed.trans ((ExecutionState.executionState_mapClassical_comp state
    (fun entry => ((step base noQuantum N input entry.1).1,
      (entry.2, (step base noQuantum N input entry.1).2)))
    (fun entry => entry.1.read
      (.storage (Batch.factorRef base noQuantum N).toCStorageRef))).trans ?_)
  apply ExecutionState.mapClassical_eq_of_support
  intro entry positive
  exact (nativeOracle_batchRecovery_value base noQuantum N input
    (NativeBatchRecovery.decodeSource (entry.1.read (Batch.sourceRead base noQuantum N))) entry.1
    (sampled_parameter base noQuantum N input state normalized sourceLaw entry positive)).trans
      (packed_read base noQuantum N entry.1).symm

attribute [local irreducible] NativeBatchRecovery.packedValue

private theorem recovered_source {origin : RuntimeCtx .quantum}
    (sampler : Circuit origin (Batch.context base noQuantum N)) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State origin Reference History) (normalized : state.IsNormalized)
    (sourceLaw : (((sampler.execute Reference state).toPMF
      ((sampler.execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read (Batch.sourceRead base noQuantum N))) =
      NativeBatch.sourceDistribution input) :
    ((((sampler.seq (into base noQuantum N input)).execute Reference state).toPMF
      (((sampler.seq (into base noQuantum N input)).execute_mass Reference state).trans
        normalized)).map (fun entry =>
          entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))) =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  have beforeNormalized := (sampler.execute_mass Reference state).trans normalized
  have observed := (sequence_read sampler (into base noQuantum N input) state
    (fun store => store.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))).trans
      (recovery_read base noQuantum N input (sampler.execute Reference state)
        beforeNormalized sourceLaw)
  have distribution := observed_pmf_congr
    ((sampler.seq (into base noQuantum N input)).execute Reference state)
    (sampler.execute Reference state)
    (((sampler.seq (into base noQuantum N input)).execute_mass Reference state).trans normalized)
    beforeNormalized
    (fun entry => entry.1.read (.storage (Batch.factorRef base noQuantum N).toCStorageRef))
    (fun entry => NativeBatchRecovery.packedValue
      (entry.1.read (Batch.sourceRead base noQuantum N))) observed
  refine distribution.trans ?_
  have pushed := map_law
    ((sampler.execute Reference state).toPMF beforeNormalized)
    (fun entry => entry.1.read (Batch.sourceRead base noQuantum N))
    (NativeBatchRecovery.packedValue (N := N))
    (NativeBatch.sourceDistribution input)
    ((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
    sourceLaw (NativeBatchRecovery.sourceDistribution_map_packedValue input)
  exact pushed

/-- The real first batch and original recovery have the original optional factor distribution. -/
theorem nativeOracle_batchRecovery_run_outputDistribution (input : Input N)
    {Reference : Register} (original : Execution.Input base Reference) :
    (run base noQuantum N input).outputDistribution original =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  let entered : State base Reference (Store base) :=
    original.state.mapClassical (fun store => (store, store))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun store => (store, store))
  exact recovered_source base noQuantum N (Batch.code base noQuantum N input) input
    entered normalized
    (nativeOracle_batch_source_toPMF base noQuantum N input entered normalized)

/-- Every later redraw, paid bank reuse and recovery has the same factor law on arbitrary input. -/
theorem nativeOracle_batchRecovery_nextRun_outputDistribution (input : Input N)
    {Reference : Register}
    (original : Execution.Input (Batch.context base noQuantum N) Reference) :
    (nextRun base noQuantum N input).outputDistribution original =
      (sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue := by
  let entered : State (Batch.context base noQuantum N) Reference
      (Store (Batch.context base noQuantum N)) :=
    original.state.mapClassical (fun store => (store, store))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun store => (store, store))
  exact recovered_source base noQuantum N (Batch.nextBatch base noQuantum N input) input
    entered normalized
    (nativeOracle_batch_next_source_toPMF base noQuantum N input entered normalized)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery
