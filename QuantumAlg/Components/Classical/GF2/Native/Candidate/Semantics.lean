/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Complete records of actual pivot-record candidate construction

Each actual pivot bit, masked coefficient and equality bit is read from its
real chronological store. The original two outer scopes and possible column
scope preserve every complete caller-store, reference and history block.
No valid pivot, free-mask, zero-source or input-alias premise is required.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private lemma operation_execute {input output : CShape} (op : ClassicalOp input output ctx ctx)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (BitWord.instruction (execution := model) op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := BitWord.instructionStep (execution := model) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  BitWord.bitWord_instruction_execute (environment := environment) (execution := model) op state

omit [BitWord.Selected model] in
private lemma idle_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.id (allowAllocation := true) (model := model) ctx).execute environment Reference state
      =
      state.mapClassical (fun entry => (entry.1, (entry.2.1, (entry.2.2, ())))) := by
  exact (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
    (model := model) Reference state).trans
    (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual equality result selects the same original column-materialization record. -/
def candidateCoefficientChoiceStep (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (candidateCoefficientChoice candidate column value).Path :=
  match value with
  | .bit false => materializePivotColumnStep candidate column store
  | .bit true => (store, ())

private lemma coefficient_execute (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateCoefficientChoice (model := model) candidate column value).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((candidateCoefficientChoiceStep candidate column value entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidateCoefficientChoiceStep candidate column value entry.1).2)))) := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_execute (model := model) candidate column Reference state
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual masked row and equality writes precede the original coefficient branch. -/
def candidateRowBodyStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (candidateRowBody matrix free candidate zero work flag row column).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (candidateMaskOp matrix free work row))
    (.seq (BitWord.instruction (execution := model) (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)))
    (BitWord.instructionStep (execution := model) (candidateMaskOp matrix free work row))
    (Circuit.sequenceStoreRecord
      (BitWord.instruction (execution := model) (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column))
      (BitWord.instructionStep (execution := model) (decisionEqualityOp work zero flag))
      (fun current =>
        let value := current.read (.storage flag.toCStorageRef)
        let actual := candidateCoefficientChoiceStep candidate column value current
        (actual.1, ⟨value, actual.2⟩))) store

/-- The selected-row body preserves its full actual store/reference/history transformation. -/
lemma gf2CandidateRowBody_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateRowBody (model := model) matrix free candidate zero work flag row column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((candidateRowBodyStep matrix free candidate zero work flag row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidateRowBodyStep matrix free candidate zero work flag row column entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (candidateMaskOp matrix free work row))
    (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
      (operation_execute (decisionEqualityOp work zero flag))
      (fun reference {_} _ current => Circuit.execute_branchStoreRecord
        (environment := environment) (model := model)
        (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)
        (candidateCoefficientChoiceStep candidate column) (coefficient_execute candidate column)
        reference current)) Reference state

/-- The real equality latch is initialized and popped around the complete selected-row body. -/
def scopedCandidateRowStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store (pivotMaskContext ctx width)) :
    Store (pivotMaskContext ctx width) ×
      (scopedCandidateRow matrix free candidate zero row column).Path
      :=
  let actual := candidateRowBodyStep (decisionWrite width matrix) (decisionWrite width free)
    (decisionWrite width candidate) (decisionWrite width zero) (decisionWork ctx width)
    (pivotLatch (pivotMaskContext ctx width)) row column
    (store.pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
      (pivotMaskContext ctx width).canonicalFreshKey_fresh)
  (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
    (pivotMaskContext ctx width).canonicalFreshKey_fresh actual.1, actual.2)

private lemma scopedCandidateRow_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference (model.HiddenState × History)) :
    (scopedCandidateRow (model := model) matrix free candidate zero row column).execute environment
        Reference state =
      state.mapClassical (fun entry =>
        ((scopedCandidateRowStep matrix free candidate zero row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (scopedCandidateRowStep matrix free candidate zero row column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (gf2CandidateRowBody_execute (model := model) _ _ _ _ _ _ row column) Reference state

/-- The original masked word encloses the actual flag and possible column-mask scopes. -/
def candidateRowSelectedStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (candidateRowSelected matrix free candidate zero row column).Path :=
  let actual := scopedCandidateRowStep matrix free candidate zero row column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The actual selected row releases all internal cells and preserves every original correlation. -/
lemma gf2CandidateRowSelected_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateRowSelected (model := model) matrix free candidate zero row column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((candidateRowSelectedStep matrix free candidate zero row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidateRowSelectedStep matrix free candidate zero row column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (scopedCandidateRow_execute (model := model) matrix free candidate zero row column)
    Reference state

/-- The original pivot-record bit chooses its actual scoped row or the unchanged caller store. -/
def candidatePivotChoiceStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (candidatePivotChoice matrix free candidate zero row column value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => candidateRowSelectedStep matrix free candidate zero row column store

private lemma pivotChoice_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePivotChoice (model := model) matrix free candidate zero row column value).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((candidatePivotChoiceStep matrix free candidate zero row column value entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidatePivotChoiceStep matrix free candidate zero row column value entry.1).2))))
          := by
  cases value with
  | bit value =>
      cases value
      · refine (idle_execute (model := model) Reference state).trans ?_
        exact ExecutionState.executionState_mapClassical_congr _ rfl
      · exact gf2CandidateRowSelected_execute (model := model) matrix free candidate zero row column
          Reference state

/-- The complete row record starts with the actual MSB-first column-to-row pivot lookup. -/
def candidatePivotRowStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (candidatePivotRow matrix rows free candidate zero row column).Path :=
  let value := store.read (eliminationBit rows column row)
  let actual := candidatePivotChoiceStep matrix free candidate zero row column value store
  (actual.1, ⟨value, actual.2⟩)

/-- The actual pivot-record branch controls the full original row transformation. -/
lemma gf2CandidatePivotRow_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePivotRow (model := model) matrix rows free candidate zero row column).execute
      environment
        Reference state =
      state.mapClassical (fun entry =>
        ((candidatePivotRowStep matrix rows free candidate zero row column entry.1).1,
          (entry.2.1, (entry.2.2,
            (candidatePivotRowStep matrix rows free candidate zero row column entry.1).2))))
            :=
  Circuit.execute_branchStoreRecord
    (environment := environment) (model := model) (eliminationBit rows column row)
    (candidatePivotChoice (model := model) matrix free candidate zero row column)
    (candidatePivotChoiceStep matrix free candidate zero row column)
    (pivotChoice_execute (model := model) matrix free candidate zero row column) Reference state

/-- The actual free-mask copy precedes the original column-major chronological row records. -/
def buildCandidateStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (buildCandidate matrix rows free candidate zero).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow (model := model) matrix rows free candidate zero row column)))
    (BitWord.instructionStep (execution := model) (candidateCopyOp free candidate))
    (Circuit.forRangeStoreRecord width _ (fun column => Circuit.forRangeStoreRecord rowCount _
      (fun row => candidatePivotRowStep matrix rows free candidate zero row column))) store

/-- Original copy and both actual traversals preserve every complete input state correlation. -/
lemma gf2BuildCandidate_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (buildCandidate (model := model) matrix rows free candidate zero).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((buildCandidateStep matrix rows free candidate zero entry.1).1,
          (entry.2.1, (entry.2.2,
            (buildCandidateStep matrix rows free candidate zero entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (operation_execute (candidateCopyOp free candidate))
    (Circuit.execute_forRangeStoreRecord
      (environment := environment) (model := model) width _ _ (fun column =>
      Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) rowCount _ _
        (fun row => gf2CandidatePivotRow_execute (model := model)
          matrix rows free candidate zero row column)))
    Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
