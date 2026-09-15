/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Context
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Retained.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Scope.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Readout
import all QuantumAlg.Core.Execution.Store

/-!
# Native factor recovery reads the actual source transcript

Each parameter and phase comes from its genuine retained sample tuple. The
new result key is disjoint from all of those tuples, and the existing scoped
scan supplies and releases every internal scratch cell. Thus its actual
result is the original first present factor for that same source transcript,
with no separation or initial scratch values supplied by a caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

private def sourceEntries {N count : Nat} (samples : List.Vector (SourceOutcome N) count) :
    List (NativeFactorScan.Inputs (post N count) N × SourceOutcome N) :=
  List.ofFn (fun index => (visitInput N count index, samples.get index))

private theorem sourceEntries_inputs {N count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    (sourceEntries samples).map Prod.fst = visitInputs N count := by
  simp only [sourceEntries, visitInputs, List.map_ofFn, Function.comp_def]

private theorem sourceEntries_outcomes {N count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    (sourceEntries samples).map Prod.snd = samples.toList := by
  calc
    (sourceEntries samples).map Prod.snd = List.ofFn samples.get := by
      simp only [sourceEntries, List.map_ofFn, Function.comp_def]
    _ = samples.toList := (List.Vector.toList_ofFn samples.get).symm.trans
      (congrArg List.Vector.toList (List.Vector.ofFn_get samples))

private theorem sourceEntries_outputFree {N count : Nat}
    (samples : List.Vector (SourceOutcome N) count) :
    ∀ entry ∈ sourceEntries samples,
      (resultRef N count).key ∉ entry.1.parameter.storageKeys ∧
        (resultRef N count).key ∉ entry.1.phase.storageKeys := by
  intro entry member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨result_tuple_separate N count index, result_tuple_separate N count index⟩

/-- The actual retained result allocation preserves each complete original source tuple. -/
theorem recovery_tuple_read {N count : Nat} (source : Input N)
    (store : Store (sampledContext N count)) (samples : List.Vector (SourceOutcome N) count)
    (sampled : store.read
      (NativeBatch.readout (NativeBank.context pre pre_quantumWires N) N count) =
        NativeSourceReadout.encoding source samples) (index : Fin count) :
    (store.pushRetained (resultKey N count) (outputShape N) (resultFresh N count)).read
      (tupleInput N count index) = NativeBatch.sourceValue source (samples.get index) :=
  (tupleInput_read N count index store).trans
    (congrArg (fun value => value.get index) sampled)

private theorem sourceEntries_represented {N count : Nat} (source : Input N)
    (store : Store (sampledContext N count)) (samples : List.Vector (SourceOutcome N) count)
    (sampled : store.read
      (NativeBatch.readout (NativeBank.context pre pre_quantumWires N) N count) =
        NativeSourceReadout.encoding source samples) :
    NativeFactorScan.Represents source (sourceEntries samples)
      (store.pushRetained (resultKey N count) (outputShape N) (resultFresh N count)) := by
  intro entry member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  have actual := recovery_tuple_read source store samples sampled index
  exact ⟨congrArg (fun value => value.second.first) actual,
    congrArg (fun value => value.second.second) actual⟩

/-- The actual full recovery tail returns the first source factor for its stored transcript. -/
theorem recoveryStep_output_of_source {N count : Nat} (source : Input N)
    (store : Store (sampledContext N count)) (samples : List.Vector (SourceOutcome N) count)
    (sampled : store.read
      (NativeBatch.readout (NativeBank.context pre pre_quantumWires N) N count) =
        NativeSourceReadout.encoding source samples) :
    (recoveryStep source count store).1.read (.storage (resultRef N count).toCStorageRef) =
      NativeFactorScan.sourceResults source samples.toList := by
  let entered := store.pushRetained
    (resultKey N count) (outputShape N) (resultFresh N count)
  have actual := NativeFactorScan.Scope.result source (sourceEntries samples)
    (resultRef N count) entered (sourceEntries_outputFree samples)
    (sourceEntries_represented source store samples sampled)
  have sameStore : (NativeFactorScan.Scope.step source
      ((sourceEntries samples).map Prod.fst) (resultRef N count) entered).1 =
        (NativeFactorScan.Scope.step source (visitInputs N count)
          (resultRef N count) entered).1 :=
    congrArg (fun inputs =>
      (NativeFactorScan.Scope.step source inputs (resultRef N count) entered).1)
      (sourceEntries_inputs samples)
  refine (congrArg (fun final : Store (post N count) =>
    final.read (.storage (resultRef N count).toCStorageRef)) sameStore.symm).trans ?_
  exact actual.trans (congrArg (NativeFactorScan.sourceResults source)
    (sourceEntries_outcomes samples))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
