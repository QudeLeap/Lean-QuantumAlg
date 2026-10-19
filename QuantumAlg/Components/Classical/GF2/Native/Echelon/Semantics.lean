/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Echelon
import all QuantumAlg.Components.Classical.GF2.Native.Load.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Semantics

/-!
# Complete records of actual GF(2) matrix reduction

The original initialization writes precede every actual column record.
All complete caller-store, quantum-reference and old-history correlations
follow the same real intermediate stores and lexical entry and exit.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Each original initialization vector write consumes the same actual source word. -/
def pivotRowsClearBodyStep
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (store : Store ctx) :
    Store ctx × (pivotRowsClearBody rows zero).Path :=
  Circuit.forRangeStoreRecord width
    (fun column => BitWord.instruction (execution := model) (pivotRowWriteOp rows zero column))
    (fun column => BitWord.instructionStep (execution := model)
      (pivotRowWriteOp rows zero column)) store

/-- Ordered real vector writes preserve every complete quantum-reference and history block. -/
lemma gf2PivotRowsClearBody_execute
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (pivotRowsClearBody (model := model) rows zero).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((pivotRowsClearBodyStep rows zero entry.1).1,
        (entry.2.1, (entry.2.2, (pivotRowsClearBodyStep rows zero entry.1).2)))) :=
  Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) width _ _
    (fun column _ {_} _ current => BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model)
      (pivotRowWriteOp rows zero column) current) Reference state

/-- The actual fresh zero row word is allocated once and popped after all vector writes. -/
def clearPivotRowsStep (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (store : Store ctx) : Store ctx × (clearPivotRows rows).Path :=
  let actual := pivotRowsClearBodyStep
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount)
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The initialization scope has its complete actual store/reference/history equation. -/
lemma gf2ClearPivotRows_execute
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (clearPivotRows (model := model) rows).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((clearPivotRowsStep rows entry.1).1,
          (entry.2.1, (entry.2.2, (clearPivotRowsStep rows entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (environment := environment) (model := model) _ _ _ _ _
    (gf2PivotRowsClearBody_execute (model := model) _ _) Reference state

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width))

/-- Both real self-XORs and pivot-row initialization feed the complete actual column traversal. -/
def reduceMatrixStep (store : Store ctx) :
    Store ctx × (reduceMatrix matrix used rows columns).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
    (.seq (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (.seq (clearPivotRows (model := model) rows)
        (Circuit.forRange width
          (reduceColumn (model := model) matrix used rows columns))))
    (BitWord.instructionStep (execution := model) (Word.PowerOfTwo.clearOp used))
    (Circuit.sequenceStoreRecord
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (.seq (clearPivotRows (model := model) rows)
        (Circuit.forRange width
          (reduceColumn (model := model) matrix used rows columns)))
      (BitWord.instructionStep (execution := model) (Word.PowerOfTwo.clearOp columns))
      (Circuit.sequenceStoreRecord (clearPivotRows (model := model) rows)
        (Circuit.forRange width (reduceColumn (model := model) matrix used rows columns))
        (clearPivotRowsStep rows)
        (Circuit.forRangeStoreRecord width
          (reduceColumn (model := model) matrix used rows columns)
          (reduceColumnStep matrix used rows columns)))) store

/-- Every complete actual column record follows the original real initialization stages. -/
lemma gf2ReduceMatrix_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduceMatrix (model := model) matrix used rows columns).execute environment Reference state =
      state.mapClassical (fun entry =>
      ((reduceMatrixStep matrix used rows columns entry.1).1,
        (entry.2.1, (entry.2.2,
          (reduceMatrixStep matrix used rows columns entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (fun _ {_} _ current => BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model)
      (Word.PowerOfTwo.clearOp used) current)
    (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
      (fun _ {_} _ current => BitWord.bitWord_instruction_execute
        (environment := environment) (execution := model)
        (Word.PowerOfTwo.clearOp columns) current)
      (Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
        (gf2ClearPivotRows_execute (model := model) rows)
        (Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) width _ _
          (gf2ReduceColumn_execute (model := model) matrix used rows columns)))) Reference state

/-- The actual matrix-loading record feeds the actual initialized reduction record. -/
def loadAndReduceStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (store : Store ctx) : Store ctx × (loadAndReduce input matrix used rows columns).Path :=
  Circuit.sequenceStoreRecord (loadMatrix (model := model) input matrix)
    (reduceMatrix (model := model) matrix used rows columns)
    (loadMatrixStep (model := model) input matrix)
    (reduceMatrixStep matrix used rows columns) store

/-- The original loading and reduction prefix preserves arbitrary complete old correlations. -/
lemma gf2LoadAndReduce_execute (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadAndReduce (model := model) input matrix used rows columns).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((loadAndReduceStep matrix used rows columns input entry.1).1,
          (entry.2.1, (entry.2.2,
            (loadAndReduceStep matrix used rows columns input entry.1).2)))) :=
  Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (gf2LoadMatrix_execute (model := model) input matrix)
    (gf2ReduceMatrix_execute (model := model) matrix used rows columns) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
