/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Retained.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared.Support
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Execution
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.MappedTail
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Measure.Distribution

/-!
# The complete native Shor run has the original source recovery law

The real recovery tail maps the actual sampling records while retaining their
full quantum-reference blocks. Its result equation applies on actual support,
where the original source transcript is proved from the true Born law.
Complete Output therefore reads exactly the original first present source
factor after the original independent samples and all actual recovery steps.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual recovery appends its true store and path to the existing sampling record. -/
def recoveredRecord {N : Nat} (source : Input N) (count : Nat)
    (record : (NativePreparedBatch.run pre pre_quantumWires N count).Record) :
    (run source count).Record :=
  ((recoveryStep source count record.1).1,
    (record.2.1, (record.2.2, (recoveryStep source count record.1).2)))

/-- Mathematical interpretation of source tuples; the executed tail uses their actual cells. -/
def recoveredValue {N : Nat} (source : Input N) (count : Nat)
    (value : (CShape.fixedVector count (NativeIteration.resultShape N)).Value) :
    (outputShape N).Value :=
  NativeFactorScan.sourceResults source (NativeSourceReadout.outcomes N count value).toList

/-- The one real circuit maps exactly the same actual sampling blocks through native recovery. -/
theorem execute_eq_map {N : Nat} (source : Input N) (count : Nat) (Reference : Register)
    (state : ExecutionState (Store pre) (Register.prod pre.register Reference)) :
    (run source count).execute Reference state =
      ((NativePreparedBatch.run pre pre_quantumWires N count).execute Reference state).mapClassical
        (recoveredRecord source count) := by
  refine (Circuit.execute_seq_retained_mapClassical_tail
    (resultKey N count) (outputShape N) (resultFresh N count)
    (NativePreparedBatch.code pre pre_quantumWires N count)
    (recoveryStage source count) (recoveryStep source count)
    (recoveryStage_execute source count) Reference
    (state.mapClassical (fun store => (store, store)))).trans ?_
  exact congrArg (fun decision : DecidableEq (run source count).Record =>
    @ExecutionState.mapClassical
      (NativePreparedBatch.run pre pre_quantumWires N count).Record (run source count).Record _ _
      (Register.prod (sampledContext N count).register Reference) decision
      ((NativePreparedBatch.run pre pre_quantumWires N count).execute Reference state)
      (recoveredRecord source count)) (Subsingleton.elim _ _)

/-- The complete record PMF follows the store and path update of the genuine recovery circuit. -/
theorem executionDistribution_eq_map {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run source count).executionDistribution input =
      ((NativePreparedBatch.run pre pre_quantumWires N count).executionDistribution input).map
        (recoveredRecord source count) := by
  apply PMF.ext
  intro record
  change ENNReal.ofReal ((((run source count).execute Reference input.state).block record).mass) = _
  rw [execute_eq_map]
  exact congrArg (fun distribution : PMF (run source count).Record => distribution record)
    (ExecutionState.toPMF_mapClassical
      ((NativePreparedBatch.run pre pre_quantumWires N count).execute Reference input.state)
      ((NativePreparedBatch.run pre pre_quantumWires N count).execute_normalized input)
      (recoveredRecord source count))

/-- Every supported actual record yields the original recovery of its own complete transcript. -/
theorem recoveredRecord_result {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference)
    (record : (NativePreparedBatch.run pre pre_quantumWires N count).Record)
    (supported : record ∈
      ((NativePreparedBatch.run pre pre_quantumWires N count).executionDistribution
        input).support) :
    (run source count).result (recoveredRecord source count record) =
      recoveredValue source count
        ((NativePreparedBatch.run pre pre_quantumWires N count).result record) := by
  obtain ⟨samples, sampled⟩ := sampled_supported_source source count input record supported
  refine (recoveryStep_output_of_source source record.1 samples sampled).trans ?_
  change NativeFactorScan.sourceResults source samples.toList =
    NativeFactorScan.sourceResults source
      (NativeSourceReadout.outcomes N count
        (record.1.read
          (NativeBatch.readout (NativeBank.context pre pre_quantumWires N) N count))).toList
  rw [sampled, NativeSourceReadout.outcomes_encoding]

/-- Complete output probabilities are obtained by recovering the true stored sample vector. -/
theorem outputDistribution_eq_recovery {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run source count).outputDistribution input =
      ((NativePreparedBatch.run pre pre_quantumWires N count).outputDistribution input).map
        (recoveredValue source count) := by
  change ((run source count).executionDistribution input).map (run source count).result =
    (((NativePreparedBatch.run pre pre_quantumWires N count).executionDistribution input).map
      (NativePreparedBatch.run pre pre_quantumWires N count).result).map
        (recoveredValue source count)
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  apply PMF.ext
  intro output
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro record
  by_cases supported : record ∈
      ((NativePreparedBatch.run pre pre_quantumWires N count).executionDistribution input).support
  · rw [Function.comp_apply, Function.comp_apply,
      recoveredRecord_result source count input record supported]
  · have absent := (PMF.apply_eq_zero_iff _ record).2 supported
    simp only [absent, ite_self]

/-- The full native run has precisely the original independent sampling and recovery law. -/
theorem outputDistribution_eq {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run source count).outputDistribution input =
      (PMF.independentReplicateVector (sourceOutcomePMF source) count).map
        (fun samples => NativeFactorScan.sourceResults source samples.toList) := by
  rw [outputDistribution_eq_recovery source count input,
    sampled_outputDistribution source count input, PMF.map_comp]
  apply congrArg (fun transform =>
    (PMF.independentReplicateVector (sourceOutcomePMF source) count).map transform)
  funext samples
  change NativeFactorScan.sourceResults source
    (NativeSourceReadout.outcomes N count (NativeSourceReadout.encoding source samples)).toList = _
  rw [NativeSourceReadout.outcomes_encoding]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
