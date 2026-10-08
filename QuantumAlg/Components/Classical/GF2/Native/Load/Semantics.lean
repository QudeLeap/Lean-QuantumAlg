/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Load
import all QuantumAlg.Components.Classical.TerminalDecode.FoldSemantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Record
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Complete records of the actual GF(2) matrix loader

Records follow the real clear, decoder and matrix write on their intermediate
stores. Lexical entry and exit retain the decoder's actual path. Every
quantum-reference block and old history follows the same classical map.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Actual append record for the same big-endian row decoder. -/
def rowDecodeStep (input : CInputRef ctx (.bits width))
    (loader : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (TerminalDecode.into (model := model) .bigEndian input loader).Path :=
  TerminalDecode.foldStep (model := model) loader
    (List.ofFn (fun index => CInputRef.bitsGet input index)) store

private theorem rowDecode_execute (input : CInputRef ctx (.bits width))
    (loader : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (TerminalDecode.into (model := model) .bigEndian input loader).execute Reference state =
      state.mapClassical (fun entry =>
        ((rowDecodeStep input loader entry.1).1,
          (entry.2.1, (entry.2.2, (rowDecodeStep input loader entry.1).2)))) :=
  TerminalDecode.terminalDecode_fold_execute (model := model) loader _ Reference state

/-- The real cleared word is decoded before the actual vector update occurs. -/
def rowBodyStep (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (rowBody input row matrix loader).Path :=
  Circuit.sequenceStoreRecord (BitWord.instruction (execution := model) (rowClearOp loader))
    (.seq (TerminalDecode.into (model := model) .bigEndian input loader)
      (BitWord.instruction (execution := model) (rowWriteOp row matrix loader)))
    (BitWord.instructionStep (execution := model) (rowClearOp loader))
    (Circuit.sequenceStoreRecord
      (TerminalDecode.into (model := model) .bigEndian input loader)
      (BitWord.instruction (execution := model) (rowWriteOp row matrix loader))
      (rowDecodeStep (model := model) input loader)
      (BitWord.instructionStep (execution := model) (rowWriteOp row matrix loader))) store

/-- The original row sequence maps every complete reference and history block exactly. -/
theorem gf2RowBody_execute (input : CInputRef ctx (.bits width)) (row : Fin rowCount)
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (loader : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (rowBody (model := model) input row matrix loader).execute Reference state =
      state.mapClassical (fun entry =>
        ((rowBodyStep input row matrix loader entry.1).1,
          (entry.2.1, (entry.2.2, (rowBodyStep input row matrix loader entry.1).2)))) := by
  exact Circuit.execute_sequenceStoreRecord (model := model)
    (BitWord.instruction (execution := model) (rowClearOp loader))
    (.seq (TerminalDecode.into (model := model) .bigEndian input loader)
      (BitWord.instruction (execution := model) (rowWriteOp row matrix loader)))
    (BitWord.instructionStep (execution := model) (rowClearOp loader))
    (Circuit.sequenceStoreRecord
      (TerminalDecode.into (model := model) .bigEndian input loader)
      (BitWord.instruction (execution := model) (rowWriteOp row matrix loader))
      (rowDecodeStep (model := model) input loader)
      (BitWord.instructionStep (execution := model) (rowWriteOp row matrix loader)))
    (fun _ {_} _ current =>
      BitWord.bitWord_instruction_execute (execution := model) (rowClearOp loader) current)
    (Circuit.execute_sequenceStoreRecord (model := model)
      (TerminalDecode.into (model := model) .bigEndian input loader)
      (BitWord.instruction (execution := model) (rowWriteOp row matrix loader))
      (rowDecodeStep (model := model) input loader)
      (BitWord.instructionStep (execution := model) (rowWriteOp row matrix loader))
      (rowDecode_execute input loader)
      (fun _ {_} _ current => BitWord.bitWord_instruction_execute (execution := model)
        (rowWriteOp row matrix loader) current)) Reference state

/-- The row's actual lexical scope initializes one word and pops it after its real write. -/
def loadRowStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (store : Store ctx) : Store ctx × (loadRow input matrix row).Path :=
  let actual := rowBodyStep
    ((CInputRef.vectorGet input row).underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh) row
    (matrix.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (rowCell ctx width)
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh actual.1, actual.2)

/-- The lexical loader has the complete original-store/reference execution law. -/
theorem gf2LoadRow_execute (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (row : Fin rowCount)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadRow (model := model) input matrix row).execute Reference state =
      state.mapClassical (fun entry =>
      ((loadRowStep input matrix row entry.1).1,
        (entry.2.1, (entry.2.2, (loadRowStep input matrix row entry.1).2)))) :=
  Circuit.execute_workspaceStoreRecord (model := model) _ _ _ _ _
    (gf2RowBody_execute (model := model) _ _ _ _) Reference state

/-- All row updates and paths follow the real increasing-index loop. -/
def loadMatrixStep (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (store : Store ctx) :
    Store ctx × (loadMatrix input matrix).Path :=
  Circuit.forRangeStoreRecord rowCount (loadRow (model := model) input matrix)
    (loadRowStep (model := model) input matrix) store

/-- The whole matrix loader retains arbitrary old Store, Reference and History correlations. -/
theorem gf2LoadMatrix_execute (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width))) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadMatrix (model := model) input matrix).execute Reference state =
      state.mapClassical (fun entry =>
      ((loadMatrixStep input matrix entry.1).1,
        (entry.2.1, (entry.2.2, (loadMatrixStep input matrix entry.1).2)))) :=
  Circuit.execute_forRangeStoreRecord (model := model) rowCount _ _
    (gf2LoadRow_execute (model := model) input matrix) Reference state

end

end QuantumAlg.ClassicalRoutines.GF2.Native
