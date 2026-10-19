/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Scope.Store
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Result
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Frame
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual scan geometry discharges every selector and scratch condition

The four genuine fresh cells prove all selector separations and preserve the
original sampled input frame. The surviving output is the only original
write destination. Real scope entry supplies the actual source reads, and
real release exposes the first original source factor in that output cell.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private lemma scratch_output_ne
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (index : Fin 4) :
    (scratchKeys ctx N).get index ≠ (liftWrite (N := N) result).key := by
  have actual : (scratchKeys ctx N ++ ctx.keys).Nodup := by
    rw [← context_keys]
    exact (context ctx N).keysNodup
  have present : result.key ∈ ctx.keys :=
    CInputRef.storageKeys_subset_context (.storage result.toCStorageRef)
      (List.mem_singleton_self result.key)
  intro same
  have equality : (scratchKeys ctx N).get index = result.key := same
  exact actual.disjoint (List.get_mem (scratchKeys ctx N) index) (equality.symm ▸ present)

/-- Every selector condition follows from actual allocation identities, including shared scratch. -/
lemma separated (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    NativeFactorScan.Separated (cells ctx N) (liftWrite result) where
  selector := selector_separated ctx N
  candidateAccepted := scratchKeys_ne ctx N 3 2 (by decide)
  candidateSelected := scratchKeys_ne ctx N 3 1 (by decide)
  resultAccepted := (scratch_output_ne result 2).symm
  resultSelected := (scratch_output_ne result 1).symm

/-- Every original operand avoids all four real scratch writes; only its result support matters. -/
lemma frame_free (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {shape : CShape} (other : CInputRef ctx shape) (resultFree : result.key ∉ other.storageKeys) :
    NativeFactorScan.FrameFree (cells ctx N) (liftWrite result) (liftInput other) := by
  constructor
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (3 : Fin 4))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (2 : Fin 4))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (1 : Fin 4))
  · exact scratchKeys_input_separate other _
      (List.get_mem (scratchKeys ctx N) (0 : Fin 4))
  · rw [liftInput_keys]
    exact resultFree

private def liftEntries (entries : List (Inputs ctx N × SourceOutcome N)) :
    List (Inputs (context ctx N) N × SourceOutcome N) :=
  entries.map fun entry => (liftInputs entry.1, entry.2)

private lemma liftEntries_inputs (entries : List (Inputs ctx N × SourceOutcome N)) :
    (liftEntries entries).map Prod.fst = (entries.map Prod.fst).map liftInputs := by
  simp only [liftEntries, List.map_map, Function.comp_def]

private lemma liftEntries_outcomes (entries : List (Inputs ctx N × SourceOutcome N)) :
    (liftEntries entries).map Prod.snd = entries.map Prod.snd := by
  simp only [liftEntries, List.map_map, Function.comp_def]

private lemma enteredFrames (entries : List (Inputs ctx N × SourceOutcome N))
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (outputFree : ∀ entry ∈ entries,
      result.key ∉ entry.1.parameter.storageKeys ∧ result.key ∉ entry.1.phase.storageKeys) :
    NativeFactorScan.Frames (cells ctx N) (liftWrite result) (liftEntries entries) := by
  intro lifted member
  obtain ⟨entry, original, rfl⟩ := List.mem_map.mp member
  exact ⟨frame_free result entry.1.parameter (outputFree entry original).1,
    frame_free result entry.1.phase (outputFree entry original).2⟩

private lemma enteredRepresents (source : Input N)
    (entries : List (Inputs ctx N × SourceOutcome N)) (store : Store ctx)
    (represented : NativeFactorScan.Represents source entries store) :
    NativeFactorScan.Represents source (liftEntries entries) (enter N store) := by
  intro lifted member
  obtain ⟨entry, original, rfl⟩ := List.mem_map.mp member
  exact ⟨(enter_read entry.1.parameter store).trans (represented entry original).1,
    (enter_read entry.1.phase store).trans (represented entry original).2⟩

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The released real scan returns the first source factor with all scratch conditions internal. -/
lemma result (source : Input N) (entries : List (Inputs ctx N × SourceOutcome N))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (outputFree : ∀ entry ∈ entries,
      output.key ∉ entry.1.parameter.storageKeys ∧ output.key ∉ entry.1.phase.storageKeys)
    (represented : NativeFactorScan.Represents source entries store) :
    (step (model := model) source (entries.map Prod.fst) output store).1.read (.storage
      output.toCStorageRef) =
      sourceResults source (entries.map Prod.snd) := by
  let entered := enter N store
  have actual := NativeFactorScan.code_result (model := model) source (liftEntries entries) (cells
    ctx N)
    (liftWrite output) (separated output) entered (enteredFrames entries output outputFree)
    (enteredRepresents source entries store represented)
  have sameStore : (NativeFactorScan.step (model := model) source ((liftEntries entries).map
    Prod.fst)
      (cells ctx N) (liftWrite output) entered).1 =
        (bodyStep (model := model) source (entries.map Prod.fst) output entered).1 :=
    congrArg (fun inputs =>
      (NativeFactorScan.step (model := model) source inputs (cells ctx N) (liftWrite output)
        entered).1)
      (liftEntries_inputs entries)
  refine (leave_read (.storage output.toCStorageRef)
    (bodyStep (model := model) source (entries.map Prod.fst) output entered).1).trans ?_
  refine (congrArg (fun final : Store (context ctx N) =>
    final.read (.storage (liftWrite output).toCStorageRef)) sameStore.symm).trans ?_
  exact actual.trans (congrArg (sourceResults source) (liftEntries_outcomes entries))

/-- Every actual scan branch and matching release preserve all other original structural reads. -/
lemma read_other (source : Input N) (inputs : List (Inputs ctx N))
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    {shape : CShape} (other : CInputRef ctx shape) (outputFree : output.key ∉ other.storageKeys)
    (store : Store ctx) :
    (step (model := model) source inputs output store).1.read other = store.read other :=
  (leave_read other (bodyStep (model := model) source inputs output (enter N store)).1).trans
    ((NativeFactorScan.read_other (model := model) source (inputs.map liftInputs) (cells ctx N)
      (liftWrite output)
      (liftInput other) (frame_free output other outputFree) (enter N store)).trans
      (enter_read other store))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan.Scope
