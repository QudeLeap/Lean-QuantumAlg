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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.classical op).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.classical op).Path))
        (fun entry => (entry.1.applyOp op, (entry.2, ()))) := by
  refine (Circuit.execute_classical_mapClassical op Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.id ctx).execute Reference state =
      state.mapClassical (D := Store ctx × (History × (Circuit.id ctx).Path))
        (fun entry => (entry.1, (entry.2, ()))) := by
  refine (Circuit.execute_id_mapClassical Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private def successChoiceStep (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (value : CShape.Value .bit)
    (store : Store ctx) : Store ctx × (successChoice body value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => record store

private theorem successChoice_execute (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History), body.execute Reference state =
        state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2))))
    (value : CShape.Value .bit) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (successChoice body value).execute Reference state =
      state.mapClassical (fun entry => ((successChoiceStep body record value entry.1).1,
        (entry.2, (successChoiceStep body record value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · exact idle_execute Reference state
      · exact equation Reference state

private def whenSuccessfulStep (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (store : Store ctx) :
    Store ctx × (whenSuccessful success body).Path :=
  let value := store.read (.storage success.toCStorageRef)
  let actual := successChoiceStep body record value store
  (actual.1, ⟨value, actual.2⟩)

private theorem whenSuccessful_execute (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History), body.execute Reference state =
        state.mapClassical (fun entry => ((record entry.1).1, (entry.2, (record entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (whenSuccessful success body).execute Reference state =
      state.mapClassical (fun entry => ((whenSuccessfulStep success body record entry.1).1,
        (entry.2, (whenSuccessfulStep success body record entry.1).2))) :=
  Circuit.execute_branch_mapClassical (.storage success.toCStorageRef) (successChoice body)
    (successChoiceStep body record) (successChoice_execute body record equation) Reference state

/-- The actual terminal instruction writes the original optional encoding of current latches. -/
def packOutputStep (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width))) (store : Store ctx) :
    Store ctx × (packOutput success candidate output).Path :=
  (store.applyOp (.packOption ctx
    (.product (.storage success.toCStorageRef) (.storage candidate.toCStorageRef)) output), ())

/-- The actual packOption preserves every complete old store/reference/history correlation. -/
theorem gf2PackOutput_execute (success : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (packOutput success candidate output).execute Reference state =
      state.mapClassical (fun entry => ((packOutputStep success candidate output entry.1).1,
        (entry.2, (packOutputStep success candidate output entry.1).2))) :=
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
  (Circuit.sequenceRecord (loadAndReduce input matrix used rows columns)
  (.seq (.classical (complementPivotMaskOp columns)) (.seq (.classical (pivotFoundOp success))
    (.seq (selectUniqueFree columns zero success) (.seq (whenSuccessful success (buildCandidate
    matrix rows columns candidate zero)) (.seq (whenSuccessful success (checkCandidateNonzero
    candidate zero success)) (.seq (whenSuccessful success (validateSamples input candidate
    success)) (packOutput success candidate output)))))))
  (loadAndReduceStep matrix used rows columns input)
  (Circuit.sequenceRecord (.classical (complementPivotMaskOp columns))
  (.seq (.classical (pivotFoundOp success)) (.seq (selectUniqueFree columns zero success) (.seq
    (whenSuccessful success (buildCandidate matrix rows columns candidate zero)) (.seq
    (whenSuccessful success (checkCandidateNonzero candidate zero success)) (.seq
    (whenSuccessful success (validateSamples input candidate success)) (packOutput success
    candidate output))))))
  ((fun current => (current.applyOp (complementPivotMaskOp columns), ())))
  (Circuit.sequenceRecord (.classical (pivotFoundOp success))
  (.seq (selectUniqueFree columns zero success) (.seq (whenSuccessful success (buildCandidate
    matrix rows columns candidate zero)) (.seq (whenSuccessful success (checkCandidateNonzero
    candidate zero success)) (.seq (whenSuccessful success (validateSamples input candidate
    success)) (packOutput success candidate output)))))
  ((fun current => (current.applyOp (pivotFoundOp success), ())))
  (Circuit.sequenceRecord (selectUniqueFree columns zero success)
  (.seq (whenSuccessful success (buildCandidate matrix rows columns candidate zero)) (.seq
    (whenSuccessful success (checkCandidateNonzero candidate zero success)) (.seq
    (whenSuccessful success (validateSamples input candidate success)) (packOutput success
    candidate output))))
  (selectUniqueFreeStep columns zero success)
  (Circuit.sequenceRecord (whenSuccessful success (buildCandidate matrix rows columns candidate
    zero))
  (.seq (whenSuccessful success (checkCandidateNonzero candidate zero success)) (.seq
    (whenSuccessful success (validateSamples input candidate success)) (packOutput success
    candidate output)))
  (whenSuccessfulStep success _ (buildCandidateStep matrix rows columns candidate zero))
  (Circuit.sequenceRecord (whenSuccessful success (checkCandidateNonzero candidate zero
    success))
  (.seq (whenSuccessful success (validateSamples input candidate success)) (packOutput success
    candidate output))
  (whenSuccessfulStep success _ (checkCandidateNonzeroStep candidate zero success))
  (Circuit.sequenceRecord (whenSuccessful success (validateSamples input candidate success))
  (packOutput success candidate output)
  (whenSuccessfulStep success _ (validateSamplesStep input candidate success))
  (packOutputStep success candidate output)))))))) store

/-- The original complete same-context circuit preserves the full actual state interpretation. -/
theorem gf2Into_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into input matrix used rows columns candidate zero success output).execute Reference state =
      state.mapClassical (fun entry =>
        ((intoStep input matrix used rows columns candidate zero success output entry.1).1,
          (entry.2,
            (intoStep input matrix used rows columns candidate zero success output entry.1).2))) :=
  (Circuit.execute_sequenceRecord _ _ _ _ (gf2LoadAndReduce_execute matrix used rows columns
    input)
  (Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (complementPivotMaskOp columns))
  (Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (pivotFoundOp success))
  (Circuit.execute_sequenceRecord _ _ _ _ (gf2UniqueFree_execute columns zero success)
  (Circuit.execute_sequenceRecord _ _ _ _ (whenSuccessful_execute success _ _
    (gf2BuildCandidate_execute matrix rows columns candidate zero))
  (Circuit.execute_sequenceRecord _ _ _ _ (whenSuccessful_execute success _ _
    (gf2CandidateNonzero_execute candidate zero success))
  (Circuit.execute_sequenceRecord _ _ _ _ (whenSuccessful_execute success _ _
    (gf2ValidationSamples_execute input candidate success))
  (gf2PackOutput_execute success candidate output)))))))) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
