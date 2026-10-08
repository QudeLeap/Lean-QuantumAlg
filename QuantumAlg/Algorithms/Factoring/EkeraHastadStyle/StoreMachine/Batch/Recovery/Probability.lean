/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Recovery.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Batch.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Run.Probability

/-!
# Original batch recovery law from the actual complete execution

The original source execution supplies both the stored parameter and the
sixteen retained outcomes. Its actual output support proves that the parameter
belongs to the source decoded from those same retained bits. The deterministic
recovery tail maps the complete execution records, including their original
histories, so its output law follows from actual block probabilities without
assuming independence from an arbitrary external reference.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery

open Execution ShortDLP.CompiledMAU

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Probability maps preserve the already constructed source context as one fixed interface.
attribute [local irreducible] NativeBatch.context NativeBatch.code body tail step

private theorem map_eq_on_support {Source Target : Type} (distribution : PMF Source)
    (left right : Source → Target)
    (equal : ∀ source ∈ distribution.support, left source = right source) :
    distribution.map left = distribution.map right := by
  apply PMF.ext
  intro target
  simp only [PMF.map_apply]
  apply tsum_congr
  intro source
  by_cases supported : source ∈ distribution.support
  · rw [equal source supported]
  · have zero : distribution source = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using supported
    simp only [zero, ite_self]

private theorem result_mem_support {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (program : AlgorithmRun model pre post shape)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference)
    (record : program.Record)
    (supported : record ∈ (program.executionDistribution input).support) :
    program.result record ∈ (program.outputDistribution input).support := by
  rw [AlgorithmRun.outputDistribution, PMF.mem_support_map_iff]
  exact ⟨record, supported, rfl⟩

/-- Every supported complete source value carries the parameter of its own decoded source. -/
theorem sourceDistribution_parameter {N : Nat} (input : Input N)
    (value : (NativeBatch.resultShape N).Value)
    (supported : value ∈ (NativeBatch.sourceDistribution input).support) :
    value.second.first = parameterValue input (decodeSource value) := by
  rw [NativeBatch.sourceDistribution, PMF.mem_support_bind_iff] at supported
  rcases supported with ⟨source, _sourceSupported, outcomesSupported⟩
  rw [PMF.mem_support_map_iff] at outcomesSupported
  rcases outcomesSupported with ⟨samples, _samplesSupported, rfl⟩
  exact sourceValue_parameter input source samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- Decoding the actual source Output gives the exact pure value used by recovery. -/
theorem packedValue_sourceOutput (before : Store (NativeBatch.context base noQuantum N)) :
    packedValue ((NativeBatch.run base noQuantum N).output.eval before) =
      LatticeFixedBatchRecoveryMachine.batchValue
        (decodeSource ((NativeBatch.run base noQuantum N).output.eval before))
        (sourceTerminals base noQuantum N) before := by
  unfold packedValue recoverValue LatticeFixedBatchRecoveryMachine.batchValue
  apply congrArg (LatticeBatchRecoveryOutput.outputValue (N := N))
  apply congrArg (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N))
  apply List.Vector.ext
  intro index
  simp only [decodeSamples, decodeOutcomes, LatticePairRecoveryBatch.preparedSamples,
    List.Vector.get_map, List.Vector.get_ofFn]
  congr 1

private theorem read_middle {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {first middle last : CShape} (store : Store ctx) (firstRef : CInputRef ctx first)
    (middleRef : CInputRef ctx middle) (lastRef : CInputRef ctx last) :
    (store.read (.product firstRef (.product middleRef lastRef))).second.first =
      store.read middleRef := rfl

private theorem sourceResult_parameter_read
    (record : (NativeBatch.run base noQuantum N).Record) :
    ((NativeBatch.run base noQuantum N).result record).second.first =
      record.1.read (NativeBatch.finalParameter base noQuantum N) := by
  unfold AlgorithmRun.result NativeBatch.run NativeBatch.resultShape
  rw [Output.all_eval, OutputRead.eval_read]
  exact read_middle record.1 (NativeBatch.finalSample base noQuantum N)
    (NativeBatch.finalParameter base noQuantum N) (NativeBatch.finalResults base noQuantum N)

/-- A supported actual source record supplies the parameter needed by the recovery proof. -/
theorem sourceRecord_parameter (specification : Input N)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference)
    (record : (NativeBatch.run base noQuantum N).Record)
    (supported : record ∈
      ((NativeBatch.run base noQuantum N).executionDistribution input).support) :
    record.1.read (NativeBatch.finalParameter base noQuantum N) =
      parameterValue specification
        (decodeSource ((NativeBatch.run base noQuantum N).result record)) := by
  have observed := result_mem_support (NativeBatch.run base noQuantum N) input record supported
  rw [NativeBatch.nativeBatch_run_outputDistribution base noQuantum N specification input]
    at observed
  exact (sourceResult_parameter_read base noQuantum record).symm.trans
    (sourceDistribution_parameter specification _ observed)

/-- The actual factor read equals the pure source projection on every supported source record. -/
theorem nativeBatchRecovery_output_on_support (specification : Input N)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference)
    (record : (NativeBatch.run base noQuantum N).Record)
    (supported : record ∈
      ((NativeBatch.run base noQuantum N).executionDistribution input).support) :
    (run base noQuantum specification).output.eval
        (step base noQuantum specification (record.1, record.2.1)).1.1 =
      packedValue ((NativeBatch.run base noQuantum N).result record) := by
  exact (run_output base noQuantum specification
    (decodeSource ((NativeBatch.run base noQuantum N).result record)) record.1 record.2.1
    (sourceRecord_parameter base noQuantum specification input record supported)).trans
      (packedValue_sourceOutput base noQuantum record.1).symm

/-- Actual recovery appends its real path and preserves the original caller history. -/
def recoveryRecord (specification : Input N)
    (record : (NativeBatch.run base noQuantum N).Record) :
    (run base noQuantum specification).Record :=
  let actual := step base noQuantum specification (record.1, record.2.1)
  (actual.1.1, (actual.1.2, (record.2.2.1, (record.2.2.2, actual.2))))

-- The probability proof consumes the compiled record equations without expanding either program.
attribute [local irreducible] code

/-- The complete run maps the original source blocks by its real recovery record update. -/
theorem nativeBatchRecovery_run_execute (specification : Input N) :
    AlgorithmRun.RetainedRecord (NativeBatch.run base noQuantum N)
      (run base noQuantum specification) (recoveryRecord base noQuantum specification) := by
  unfold recoveryRecord run code
  exact AlgorithmRun.RetainedRecord.ofTail (NativeBatch.run base noQuantum N)
    (tail base noQuantum specification)
    (Output.all (context base noQuantum N)
      (.read (.storage (resultRef base noQuantum N).toCStorageRef)))
    (step base noQuantum specification) (tail_execute base noQuantum specification)

/-- Actual record probabilities are the deterministic map of the original source records. -/
theorem nativeBatchRecovery_executionDistribution (specification : Input N)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    (run base noQuantum specification).executionDistribution input =
      ((NativeBatch.run base noQuantum N).executionDistribution input).map
        (recoveryRecord base noQuantum specification) :=
  AlgorithmRun.RetainedRecord.executionDistribution_eq_map
    (NativeBatch.run base noQuantum N) (run base noQuantum specification)
    (recoveryRecord base noQuantum specification)
    (nativeBatchRecovery_run_execute base noQuantum specification) input

/-- The real source and recovery execution has the original same-source optional factor law. -/
theorem nativeBatchRecovery_run_outputDistribution (specification : Input N)
    {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles base Reference) :
    (run base noQuantum specification).outputDistribution input =
      (sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue := by
  unfold AlgorithmRun.outputDistribution
  rw [nativeBatchRecovery_executionDistribution, PMF.map_comp]
  calc
    (((NativeBatch.run base noQuantum N).executionDistribution input).map
        ((run base noQuantum specification).result ∘
          recoveryRecord base noQuantum specification)) =
        ((NativeBatch.run base noQuantum N).executionDistribution input).map
          (packedValue (N := N) ∘ (NativeBatch.run base noQuantum N).result) := by
      apply map_eq_on_support
      intro record supported
      simpa only [Function.comp_apply, AlgorithmRun.result, recoveryRecord] using
        nativeBatchRecovery_output_on_support base noQuantum specification input record supported
    _ = ((NativeBatch.run base noQuantum N).outputDistribution input).map
        (packedValue (N := N)) :=
      (PMF.map_comp (NativeBatch.run base noQuantum N).result
        ((NativeBatch.run base noQuantum N).executionDistribution input)
        (packedValue (N := N))).symm
    _ = (sampledBatchOutputPMF specification).map
        LatticeBatchRecoveryOutput.outputValue := by
      rw [NativeBatch.nativeBatch_run_outputDistribution base noQuantum N specification input,
        sourceDistribution_map_packedValue]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchRecovery
