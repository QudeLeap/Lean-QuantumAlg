/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Record

/-!
# Complete records of actual pivot-mask materialization

Each record follows the real power loader, bitwise OR and optional vector
write on its intermediate store. Both lexical exits preserve the complete
caller store, reference and history through those actual records.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The real row-mask loader is followed by both original writes on their intermediate stores. -/
def pivotRowBodyStep (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotRowBody used rows mask pivot column).Path :=
  Circuit.sequenceStoreRecord
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column)))
    (Word.PowerOfTwo.step (model := model) (rowCount - 1 - pivot.val) mask)
    (Circuit.sequenceStoreRecord
      (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column))
      (BitWord.instructionStep (execution := model) (pivotOrOp used mask))
      (BitWord.instructionStep (execution := model)
        (pivotRowWriteOp rows mask column))) store

/-- Every original row-materialization instruction acts on the complete actual state. -/
theorem gf2PivotRowBody_execute (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotRowBody (model := model) used rows mask pivot column).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotRowBodyStep used rows mask pivot column entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotRowBodyStep used rows mask pivot column entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model)
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column)))
    (Word.PowerOfTwo.step (model := model) (rowCount - 1 - pivot.val) mask)
    (Circuit.sequenceStoreRecord
      (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column))
      (BitWord.instructionStep (execution := model) (pivotOrOp used mask))
      (BitWord.instructionStep (execution := model) (pivotRowWriteOp rows mask column)))
    (Word.PowerOfTwo.into_execute (model := model) _ _)
    (Circuit.execute_sequenceStoreRecord (model := model)
      (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model) (pivotRowWriteOp rows mask column))
      (BitWord.instructionStep (execution := model) (pivotOrOp used mask))
      (BitWord.instructionStep (execution := model) (pivotRowWriteOp rows mask column))
      (fun _ {_} _ current => BitWord.bitWord_instruction_execute (execution := model)
        (pivotOrOp used mask) current)
      (fun _ {_} _ current => BitWord.bitWord_instruction_execute (execution := model)
        (pivotRowWriteOp rows mask column) current)) Reference state

/-- Actual row materialization starts with its fresh mask and pops it only after both writes. -/
def materializePivotRowStep (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (materializePivotRow used rows pivot column).Path :=
  let actual := pivotRowBodyStep
    (used.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) pivot column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The full row-mask scope maps arbitrary original store/reference/history correlations. -/
theorem gf2MaterializePivotRow_execute (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (materializePivotRow (model := model) used rows pivot column).execute Reference state =
      state.mapClassical (fun entry =>
        ((materializePivotRowStep used rows pivot column entry.1).1,
          (entry.2.1, (entry.2.2,
            (materializePivotRowStep used rows pivot column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (gf2PivotRowBody_execute (model := model) _ _ _ pivot column) Reference state

/-- The column-mask record retains the actual loader path and its original OR instruction. -/
def pivotColumnBodyStep (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) :
    Store ctx × (pivotColumnBody output mask column).Path :=
  Circuit.sequenceStoreRecord
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask))
    (Word.PowerOfTwo.step (model := model) (width - 1 - column.val) mask)
    (BitWord.instructionStep (execution := model) (pivotOrOp output mask)) store

/-- Both original column-materialization stages preserve all complete quantum-reference blocks. -/
theorem gf2PivotColumnBody_execute (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotColumnBody (model := model) output mask column).execute Reference state =
      state.mapClassical (fun entry =>
        ((pivotColumnBodyStep output mask column entry.1).1,
          (entry.2.1, (entry.2.2,
            (pivotColumnBodyStep output mask column entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (model := model)
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask))
    (Word.PowerOfTwo.step (model := model) (width - 1 - column.val) mask)
    (BitWord.instructionStep (execution := model) (pivotOrOp output mask))
    (Word.PowerOfTwo.into_execute (model := model) _ _)
    (fun _ {_} _ current => BitWord.bitWord_instruction_execute (execution := model)
      (pivotOrOp output mask) current)
    Reference state

/-- The column mask is allocated and popped independently of the completed row-mask scope. -/
def materializePivotColumnStep (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) :
    Store ctx × (materializePivotColumn output column).Path :=
  let actual := pivotColumnBodyStep
    (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx width) column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- Column materialization has the complete original-store/reference execution equation. -/
theorem gf2MaterializePivotColumn_execute (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (materializePivotColumn (model := model) output column).execute Reference state =
      state.mapClassical (fun entry =>
        ((materializePivotColumnStep output column entry.1).1,
          (entry.2.1, (entry.2.2,
            (materializePivotColumnStep output column entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (gf2PivotColumnBody_execute (model := model) _ _ column) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
