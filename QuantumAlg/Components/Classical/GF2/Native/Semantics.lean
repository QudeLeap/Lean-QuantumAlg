/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native
import all QuantumAlg.Components.Classical.GF2.Native.Echelon.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Validation.Semantics

/-!
# Complete actual records of the original GF(2) recovery sequence

Every original branch reads the current success cell, and all stages consume
the preceding real store. The final output is the original actual packOption
write. Arbitrary complete caller Store, Reference and History correlations
are preserved; no zero or successful-recovery premise is imposed here.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private theorem operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (BitWord.instruction (execution := model) op).execute Reference state =
      state.mapClassical (fun entry =>
        let result := BitWord.instructionStep (execution := model) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_instruction_execute (execution := model) op state

omit [BitWord.Selected model] in
private theorem idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (model := model) ctx).execute Reference state =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  exact (Circuit.execute_id_mapClassical (model := model) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

private def successChoiceStep (body : Circuit model ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (successChoice body value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => record store

omit [BitWord.Selected model] in
private theorem successChoice_execute (body : Circuit model ctx ctx)
    (record : Store ctx → Store ctx × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)), body.execute Reference state =
        state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2.1, (entry.2.2, (record entry.1).2)))))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (successChoice body value).execute Reference state =
      state.mapClassical (fun entry => ((successChoiceStep body record value entry.1).1,
        (entry.2.1, (entry.2.2, (successChoiceStep body record value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact equation Reference state

private def whenSuccessfulStep (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (store : Store ctx) :
    Store ctx × (whenSuccessful success body).Path :=
  let value := store.read (.storage success.toCStorageRef)
  let actual := successChoiceStep body record value store
  (actual.1, ⟨value, actual.2⟩)

omit [BitWord.Selected model] in
private theorem whenSuccessful_execute (success : CWriteRef ctx .bit)
    (body : Circuit model ctx ctx)
    (record : Store ctx → Store ctx × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)), body.execute Reference state =
        state.mapClassical (fun entry =>
          ((record entry.1).1, (entry.2.1, (entry.2.2, (record entry.1).2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (whenSuccessful success body).execute Reference state =
      state.mapClassical (fun entry => ((whenSuccessfulStep success body record entry.1).1,
        (entry.2.1, (entry.2.2, (whenSuccessfulStep success body record entry.1).2)))) :=
  Circuit.execute_branchStoreRecord (model := model) (.storage success.toCStorageRef)
    (successChoice body)
    (successChoiceStep body record) (successChoice_execute body record equation) Reference state

/-- The actual terminal instruction writes the original optional encoding of current latches. -/
def packOutputStep (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    Store ctx × (packOutput success candidate output).Path :=
  BitWord.instructionStep (execution := model) (.packOption ctx
    (.product (.storage success.toCStorageRef) (.storage candidate.toCStorageRef)) output) store

/-- The actual packOption preserves every complete old store/reference/history correlation. -/
theorem gf2PackOutput_execute (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (packOutput (model := model) success candidate output).execute Reference state =
      state.mapClassical (fun entry => ((packOutputStep success candidate output entry.1).1,
        (entry.2.1, (entry.2.2, (packOutputStep success candidate output entry.1).2)))) :=
  operation_execute _ Reference state

/-- The final actual destination contains the original packing of both current input values. -/
theorem gf2PackOutput_value (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    (packOutputStep success candidate output store).1.read (.storage output.toCStorageRef) =
      CShape.packOption
        (store.read (.product (.storage success.toCStorageRef)
          (.storage candidate.toCStorageRef))) :=
  Store.read_applyOp_output store _

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns candidate zero : CWriteRef ctx (.unsignedWord width))
  (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- The original complete actual record composes all real stages in chronological order. -/
def intoStep (store : Store ctx) :
    Store ctx × (into input matrix used rows columns candidate zero success output).Path :=
  (Circuit.sequenceStoreRecord
  (loadAndReduce (model := model) input matrix used rows columns)
  (.seq (BitWord.instruction (execution := model) (complementPivotMaskOp columns))
    (.seq (BitWord.instruction (execution := model) (pivotFoundOp success))
    (.seq (selectUniqueFree (model := model) columns zero success)
    (.seq (whenSuccessful success
      (buildCandidate (model := model) matrix rows columns candidate zero))
    (.seq (whenSuccessful success
      (checkCandidateNonzero (model := model) candidate zero success))
    (.seq (whenSuccessful success
      (validateSamples (model := model) input candidate success))
      (packOutput (model := model) success candidate output)))))))
  (loadAndReduceStep matrix used rows columns input)
  (Circuit.sequenceStoreRecord
  (BitWord.instruction (execution := model) (complementPivotMaskOp columns))
  (.seq (BitWord.instruction (execution := model) (pivotFoundOp success))
    (.seq (selectUniqueFree (model := model) columns zero success)
    (.seq (whenSuccessful success
      (buildCandidate (model := model) matrix rows columns candidate zero))
    (.seq (whenSuccessful success
      (checkCandidateNonzero (model := model) candidate zero success))
    (.seq (whenSuccessful success
      (validateSamples (model := model) input candidate success))
      (packOutput (model := model) success candidate output))))))
  (BitWord.instructionStep (execution := model) (complementPivotMaskOp columns))
  (Circuit.sequenceStoreRecord
  (BitWord.instruction (execution := model) (pivotFoundOp success))
  (.seq (selectUniqueFree (model := model) columns zero success)
    (.seq (whenSuccessful success
      (buildCandidate (model := model) matrix rows columns candidate zero))
    (.seq (whenSuccessful success
      (checkCandidateNonzero (model := model) candidate zero success))
    (.seq (whenSuccessful success
      (validateSamples (model := model) input candidate success))
      (packOutput (model := model) success candidate output)))))
  (BitWord.instructionStep (execution := model) (pivotFoundOp success))
  (Circuit.sequenceStoreRecord (selectUniqueFree (model := model) columns zero success)
  (.seq (whenSuccessful success
    (buildCandidate (model := model) matrix rows columns candidate zero))
  (.seq (whenSuccessful success
    (checkCandidateNonzero (model := model) candidate zero success))
  (.seq (whenSuccessful success
    (validateSamples (model := model) input candidate success))
    (packOutput (model := model) success candidate output))))
  (selectUniqueFreeStep columns zero success)
  (Circuit.sequenceStoreRecord (whenSuccessful success
    (buildCandidate (model := model) matrix rows columns candidate zero))
  (.seq (whenSuccessful success
    (checkCandidateNonzero (model := model) candidate zero success))
  (.seq (whenSuccessful success
    (validateSamples (model := model) input candidate success))
    (packOutput (model := model) success candidate output)))
  (whenSuccessfulStep success _ (buildCandidateStep matrix rows columns candidate zero))
  (Circuit.sequenceStoreRecord (whenSuccessful success
    (checkCandidateNonzero (model := model) candidate zero success))
  (.seq (whenSuccessful success
    (validateSamples (model := model) input candidate success))
    (packOutput (model := model) success candidate output))
  (whenSuccessfulStep success _ (checkCandidateNonzeroStep candidate zero success))
  (Circuit.sequenceStoreRecord (whenSuccessful success
    (validateSamples (model := model) input candidate success))
  (packOutput (model := model) success candidate output)
  (whenSuccessfulStep success _ (validateSamplesStep input candidate success))
  (packOutputStep success candidate output)))))))) store

/-- The original complete same-context circuit preserves the full actual state interpretation. -/
theorem gf2Into_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) input matrix used rows columns candidate zero success output).execute
        Reference state =
      state.mapClassical (fun entry =>
        ((intoStep input matrix used rows columns candidate zero success output entry.1).1,
          (entry.2.1, (entry.2.2,
            (intoStep input matrix used rows columns candidate zero success output entry.1).2)))) :=
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (gf2LoadAndReduce_execute (model := model) matrix used rows columns input)
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (operation_execute (complementPivotMaskOp columns))
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (operation_execute (pivotFoundOp success))
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (gf2UniqueFree_execute (model := model) columns zero success)
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (whenSuccessful_execute success _ _
      (gf2BuildCandidate_execute (model := model) matrix rows columns candidate zero))
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (whenSuccessful_execute success _ _
      (gf2CandidateNonzero_execute (model := model) candidate zero success))
  (Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (whenSuccessful_execute success _ _
      (gf2ValidationSamples_execute (model := model) input candidate success))
  (gf2PackOutput_execute (model := model) success candidate output)))))))) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
