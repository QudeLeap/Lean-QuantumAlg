/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Complete

/-!
# Transparent actual record of the original nonempty batch branch

The literal branch retains its initializer, complete forward traversal,
single real XGCD computation and complete reverse traversal. The exposed
record is used to attach the proved field invariants to this same original
interpreter, with every original history and reference block preserved.
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

/-- This is the literal original nonempty branch, with no change to its program or actual order. -/
def nonemptyCircuit : Circuit model ctx ctx :=
  (initialize).seq ((forward).seq ((invert).seq backward))

/-- The original actual circuit has this literal branch whenever its batch is nonempty. -/
lemma circuit_eq_nonempty (nonempty : count ≠ 0) :
    frame.circuit (model := model) spec count fits = frame.nonemptyCircuit spec count fits := by
  rw [circuit, if_neg nonempty]
  rfl

/-- Every actual intermediate Store and returned service state is retained in this record. -/
def nonemptyValueRecord : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) ×
      (frame.nonemptyCircuit (model := model) spec count fits).Path :=
  Circuit.sequenceRecord initialize ((forward).seq ((invert).seq backward))
    (Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (.wordResize width width ctx frame.one frame.work.product)))
    (Circuit.sequenceRecord forward ((invert).seq backward)
      (Circuit.preserveHiddenRecord (frame.forwardPassRecord count fits))
      (Circuit.sequenceRecord invert backward
        (Field.Native.coefficientIntoWordStep (environment := environment) spec
          (wordRead frame.work.product) frame.work.inverse)
        (Circuit.preserveHiddenRecord (frame.reversePassRecord count fits))))

/-- The exposed actual branch record keeps all original matrix blocks and arbitrary references. -/
lemma nonemptyCircuit_execute (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.nonemptyCircuit (model := model) spec count fits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.nonemptyValueRecord (environment := environment) spec count fits
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

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
