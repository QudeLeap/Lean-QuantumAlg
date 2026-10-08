/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Record

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Native fixed-width resize into the actual narrow scratch cell. -/
def resizeOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} (refs : Refs ctx N) :=
  ClassicalOp.wordResize
    (QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N))
    (modulusBits N) ctx (FirstAccepted.cellRead refs.selection.selected) refs.narrow

/-- Native optional encoding from the actual acceptance and resized payload cells. -/
def packOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} (refs : Refs ctx N) :=
  ClassicalOp.packOption ctx (.product (FirstAccepted.cellRead refs.selection.accepted)
    (FirstAccepted.cellRead refs.narrow)) refs.result

/-- Materialize the public result before the caller releases its lexical workspace. -/
def into (refs : Refs ctx N) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (resizeOp refs))
    (BitWord.instruction (execution := model) (packOp refs))

/-- Both actual stores and the chronological native path of the resize--pack sequence. -/
def step (refs : Refs ctx N) (store : Store ctx) : Store ctx × (into refs).Path :=
  let resized := BitWord.instructionStep (execution := model) (resizeOp refs) store
  let packed := BitWord.instructionStep (execution := model) (packOp refs) resized.1
  (packed.1, (resized.2, packed.2))

/-- Full native execution preserves every quantum block, external reference and history. -/
theorem into_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [into, step, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every caller read outside both actual writes survives without initialization premises. -/
theorem into_callerFrame (refs : Refs ctx N) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other := by
  simp only [step, BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.result,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.narrow]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput
