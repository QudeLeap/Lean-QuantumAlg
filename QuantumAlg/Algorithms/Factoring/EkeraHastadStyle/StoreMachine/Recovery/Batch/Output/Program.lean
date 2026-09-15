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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Native fixed-width resize into the actual narrow scratch cell. -/
def resizeOp (refs : Refs ctx N) :=
  ClassicalOp.wordResize
    (QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N))
    (modulusBits N) ctx (FirstAccepted.cellRead refs.selection.selected) refs.narrow

/-- Native optional encoding from the actual acceptance and resized payload cells. -/
def packOp (refs : Refs ctx N) :=
  ClassicalOp.packOption ctx (.product (FirstAccepted.cellRead refs.selection.accepted)
    (FirstAccepted.cellRead refs.narrow)) refs.result

/-- Materialize the public result before the caller releases its lexical workspace. -/
def into (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (.classical (resizeOp refs)) (.classical (packOp refs))

/-- Both actual stores and the chronological native path of the resize--pack sequence. -/
def step (refs : Refs ctx N) (store : Store ctx) : Store ctx × (into refs).Path :=
  ((store.applyOp (resizeOp refs)).applyOp (packOp refs), ((), ()))

/-- Full native execution preserves every quantum block, external reference and history. -/
theorem into_execute (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  simp only [into, step, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Every caller read outside both actual writes survives without initialization premises. -/
theorem into_callerFrame (refs : Refs ctx N) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other := by
  simp only [step]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.result,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids.narrow]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryOutput
