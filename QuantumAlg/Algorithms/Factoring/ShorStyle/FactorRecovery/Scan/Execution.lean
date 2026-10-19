/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Records
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution
import all QuantumAlg.Components.Classical.FirstAccepted.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Complete execution of the ordered actual factor scan

The record follows the literal finite sequence of stored input references.
Each visit records the full native factor scope and the existing selector;
the initial latch clear and final option pack are real instructions in that
same circuit. These equations retain every Store-history block and arbitrary
external quantum reference, with no initialization or separation premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open Execution ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The real nominal unpack feeds the existing selector's actual path. -/
def selectionStep (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (selection (model := model) cells result).Path :=
  let unpacked := BitWord.instructionStep (execution := model) (unpackOp cells result) store
  let selected := FirstAccepted.step (model := model) (selectorInputs cells) (selectorRefs cells)
    unpacked.1
  (selected.1, (unpacked.2, selected.2))

/-- A real factor-recovery record precedes the actual first-success latch record. -/
def visitStep (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (visit (model := model) source inputs cells result).Path :=
  let recovered := FactorRecovery.NativeFactorScope.step (model := model) source
    inputs.parameter inputs.phase result store
  let selected := selectionStep (model := model) cells result recovered.1
  (selected.1, (recovered.2, selected.2))

/-- Actual stores and paths of the literal reference list in its original order. -/
def scanStep (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) :
    (inputs : List (Inputs ctx N)) → Store ctx →
      Store ctx × (scan (model := model) source cells result inputs).Path
  | [], store => (store, ())
  | inputs :: rest, store =>
      let visited := visitStep (model := model) source inputs cells result store
      let later := scanStep source cells result rest visited.1
      (later.1, (visited.2, later.2))

/-- The real latch clear, complete scan and final nominal option write. -/
def step (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (code (model := model) source inputs cells result).Path :=
  let cleared := BitWord.instructionStep (execution := model) (clearAcceptedOp cells) store
  let scanned := scanStep (model := model) source cells result inputs cleared.1
  let packed := BitWord.instructionStep (execution := model) (packOp cells result) scanned.1
  (packed.1, (cleared.2, (scanned.2, packed.2)))

/-- Actual execution retains the complete store, hidden service and history. -/
lemma selection_execute (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selection (model := model) cells result).execute environment Reference state =
      state.mapClassical (fun entry =>
          let actual := selectionStep (model := model) cells result entry.1
          (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  unfold selection
  rw [Circuit.execute_seq, FirstAccepted.firstAccepted_execute,
    BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual execution retains the complete store, hidden service and history. -/
lemma visit_execute (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (visit (model := model) source inputs cells result).execute environment Reference state =
      state.mapClassical (fun entry =>
          let actual := visitStep (model := model) source inputs cells result entry.1
          (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  unfold visit
  rw [Circuit.execute_seq, selection_execute, FactorRecovery.NativeFactorScope.code_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual execution retains the complete store, hidden service and history. -/
lemma scan_execute (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (inputs : List (Inputs ctx N)) :
    ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      (scan (model := model) source cells result inputs).execute environment Reference state =
        state.mapClassical (fun entry =>
          let actual := scanStep (model := model) source cells result inputs entry.1
          (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  induction inputs with
  | nil =>
      intro Reference History _ state
      exact (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | cons inputs rest ih =>
      intro Reference History _ state
      change (Circuit.seq (visit (model := model) source inputs cells result)
        (scan (model := model) source cells result rest)).execute environment Reference state = _
      rw [Circuit.execute_seq, ih, visit_execute]
      simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl

private def scanPackStep (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    Store ctx × (Circuit.seq (scan (model := model) source cells result inputs)
      (BitWord.instruction (execution := model) (packOp cells result))).Path :=
  let scanned := scanStep (model := model) source cells result inputs store
  let packed := BitWord.instructionStep (execution := model) (packOp cells result) scanned.1
  (packed.1, (scanned.2, packed.2))

private lemma scanPack_execute (source : Input N) (inputs : List (Inputs ctx N))
    (cells : Cells ctx N) (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.seq (scan (model := model) source cells result inputs) (BitWord.instruction (execution
      := model) (packOp cells result))).execute
        environment Reference state = state.mapClassical (fun entry =>
          let actual := scanPackStep (model := model) source inputs cells result entry.1
          (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  rw [Circuit.execute_seq, BitWord.bitWord_instruction_execute, scan_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual execution retains the complete store, hidden service and history. -/
lemma code_execute (source : Input N) (inputs : List (Inputs ctx N)) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) source inputs cells result).execute environment Reference state =
      state.mapClassical (fun entry =>
          let actual := step (model := model) source inputs cells result entry.1
          (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  unfold code
  rw [Circuit.execute_seq, scanPack_execute, BitWord.bitWord_instruction_execute]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
