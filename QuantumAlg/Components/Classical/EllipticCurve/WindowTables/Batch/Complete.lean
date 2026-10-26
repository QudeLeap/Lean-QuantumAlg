/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Execution

/-!
# Complete actual batch instrument

The initializer, increasing prefix pass, one real coefficient computation
and decreasing overwrite pass compose on their true intermediate Stores and
service states. The empty batch is the actual identity. All original joint
quantum-reference blocks and histories are retained by the same record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length) (spec : ModulusSpec width)
  (count : Nat) (fits : count < length)

local notation "initialize" => BitWord.instruction (execution := model)
  (ClassicalOp.wordResize width width ctx frame.one frame.work.product)
local notation "forward" => frame.forwardPass (model := model) count fits
local notation "invert" => Field.Native.coefficientIntoWord (model := model) spec
  (wordRead frame.work.product) frame.work.inverse
local notation "backward" => frame.reversePass (model := model) count fits

private def finalRecord : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) × ((invert).seq backward).Path :=
  Circuit.sequenceRecord invert backward
    (Field.Native.coefficientIntoWordStep (environment := environment) spec
      (wordRead frame.work.product) frame.work.inverse)
    (Circuit.preserveHiddenRecord (frame.reversePassRecord count fits))

private def preparedRecord : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) × ((forward).seq ((invert).seq backward)).Path :=
  Circuit.sequenceRecord forward ((invert).seq backward)
    (Circuit.preserveHiddenRecord (frame.forwardPassRecord count fits))
    (finalRecord (environment := environment) frame spec count fits)

private def nonemptyRecord : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      ((initialize).seq ((forward).seq ((invert).seq backward))).Path :=
  Circuit.sequenceRecord initialize ((forward).seq ((invert).seq backward))
    (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (.wordResize width width ctx frame.one frame.work.product)))
    (preparedRecord (environment := environment) frame spec count fits)

private lemma nonempty_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((initialize).seq ((forward).seq ((invert).seq backward))).execute environment Reference
      state = state.mapClassical (fun entry =>
        let result := nonemptyRecord (environment := environment) frame spec count fits
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply Circuit.execute_sequenceRecord (environment := environment)
  · intro reference history historyFinite initial
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model) _ initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  · intro reference history historyFinite initial
    apply Circuit.execute_sequenceRecord (environment := environment)
    · intro reference history historyFinite initial
      exact (frame.forwardPass_execute count fits reference initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
    · intro reference history historyFinite initial
      apply Circuit.execute_sequenceRecord (environment := environment)
      · exact Field.Native.coefficientIntoWord_execute spec
          (wordRead frame.work.product) frame.work.inverse
      · intro reference history historyFinite initial
        exact (frame.reversePass_execute count fits reference initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- One exact record represents the complete physical classical program on every incoming state. -/
lemma circuit_actualRecord :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (frame.circuit (model := model) spec count fits).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (frame.circuit (model := model) spec count fits).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  unfold circuit
  by_cases empty : count = 0
  · rw [if_pos empty]
    refine ⟨fun before => (before, ()), ?_⟩
    intro reference history historyFinite initial
    exact (Circuit.execute_id_mapClassical (environment := environment) reference initial).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · rw [if_neg empty]
    exact ⟨nonemptyRecord (environment := environment) frame spec count fits,
      nonempty_execute (environment := environment) frame spec count fits⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
