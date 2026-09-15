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

/-- The actual equality result selects the same original column-materialization record. -/
def candidateCoefficientChoiceStep (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (candidateCoefficientChoice candidate column value).Path :=
  match value with
  | .bit false => materializePivotColumnStep candidate column store
  | .bit true => (store, ())

private theorem coefficient_execute (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateCoefficientChoice candidate column value).execute Reference state =
      state.mapClassical (fun entry =>
        ((candidateCoefficientChoiceStep candidate column value entry.1).1,
          (entry.2, (candidateCoefficientChoiceStep candidate column value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_execute candidate column Reference state
      · exact idle_execute Reference state

/-- The actual masked row and equality writes precede the original coefficient branch. -/
def candidateRowBodyStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (candidateRowBody matrix free candidate zero work flag row column).Path :=
  Circuit.sequenceRecord (.classical (candidateMaskOp matrix free work row))
    (.seq (.classical (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column)))
    (fun current => (current.applyOp (candidateMaskOp matrix free work row), ()))
    (Circuit.sequenceRecord (.classical (decisionEqualityOp work zero flag))
      (.branch (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column))
      (fun current => (current.applyOp (decisionEqualityOp work zero flag), ()))
      (fun current =>
        let value := current.read (.storage flag.toCStorageRef)
        let actual := candidateCoefficientChoiceStep candidate column value current
        (actual.1, ⟨value, actual.2⟩))) store

/-- The selected-row body preserves its full actual store/reference/history transformation. -/
theorem gf2CandidateRowBody_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateRowBody matrix free candidate zero work flag row column).execute Reference state =
      state.mapClassical (fun entry =>
        ((candidateRowBodyStep matrix free candidate zero work flag row column entry.1).1,
          (entry.2,
            (candidateRowBodyStep matrix free candidate zero work flag row column entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (candidateMaskOp matrix free work row))
    (Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (decisionEqualityOp work zero flag))
      (fun reference {_} _ current => Circuit.execute_branch_mapClassical
        (.storage flag.toCStorageRef) (candidateCoefficientChoice candidate column)
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

private theorem scopedCandidateRow_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (pivotMaskContext ctx width) Reference History) :
    (scopedCandidateRow matrix free candidate zero row column).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopedCandidateRowStep matrix free candidate zero row column entry.1).1,
          (entry.2, (scopedCandidateRowStep matrix free candidate zero row column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (gf2CandidateRowBody_execute _ _ _ _ _ _ row column) Reference state

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
theorem gf2CandidateRowSelected_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateRowSelected matrix free candidate zero row column).execute Reference state =
      state.mapClassical (fun entry =>
        ((candidateRowSelectedStep matrix free candidate zero row column entry.1).1,
          (entry.2, (candidateRowSelectedStep matrix free candidate zero row column entry.1).2))) :=
  Circuit.execute_workspace_mapClassical _ _ _ _ _
    (scopedCandidateRow_execute matrix free candidate zero row column) Reference state

/-- The original pivot-record bit chooses its actual scoped row or the unchanged caller store. -/
def candidatePivotChoiceStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (candidatePivotChoice matrix free candidate zero row column value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => candidateRowSelectedStep matrix free candidate zero row column store

private theorem pivotChoice_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidatePivotChoice matrix free candidate zero row column value).execute Reference state =
      state.mapClassical (fun entry =>
        ((candidatePivotChoiceStep matrix free candidate zero row column value entry.1).1,
          (entry.2,
            (candidatePivotChoiceStep matrix free candidate zero row column value entry.1).2)))
          := by
  cases value with
  | bit value =>
      cases value
      · exact idle_execute Reference state
      · exact gf2CandidateRowSelected_execute matrix free candidate zero row column Reference state

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
theorem gf2CandidatePivotRow_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidatePivotRow matrix rows free candidate zero row column).execute Reference state =
      state.mapClassical (fun entry =>
        ((candidatePivotRowStep matrix rows free candidate zero row column entry.1).1,
          (entry.2, (candidatePivotRowStep matrix rows free candidate zero row column entry.1).2)))
            :=
  Circuit.execute_branch_mapClassical (eliminationBit rows column row)
    (candidatePivotChoice matrix free candidate zero row column)
    (candidatePivotChoiceStep matrix free candidate zero row column)
    (pivotChoice_execute matrix free candidate zero row column) Reference state

/-- The actual free-mask copy precedes the original column-major chronological row records. -/
def buildCandidateStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (buildCandidate matrix rows free candidate zero).Path :=
  Circuit.sequenceRecord (.classical (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column)))
    (fun current => (current.applyOp (candidateCopyOp free candidate), ()))
    (Circuit.forRangeRecord width _ (fun column => Circuit.forRangeRecord rowCount _
      (fun row => candidatePivotRowStep matrix rows free candidate zero row column))) store

/-- Original copy and both actual traversals preserve every complete input state correlation. -/
theorem gf2BuildCandidate_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (buildCandidate matrix rows free candidate zero).execute Reference state =
      state.mapClassical (fun entry =>
        ((buildCandidateStep matrix rows free candidate zero entry.1).1,
          (entry.2, (buildCandidateStep matrix rows free candidate zero entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (operation_execute (candidateCopyOp free candidate))
    (Circuit.execute_forRangeRecord width _ _ (fun column =>
      Circuit.execute_forRangeRecord rowCount _ _
        (fun row => gf2CandidatePivotRow_execute matrix rows free candidate zero row column)))
    Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
