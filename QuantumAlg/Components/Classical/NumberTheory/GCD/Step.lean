/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Encoding
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual native instructions of one Euclidean remainder step

An active step divides the previous word by the current word, rotates the
current word into the previous cell, copies the remainder into the current
cell, and refreshes its stored nonzero bit. These are five ordinary closed
instructions. Their exact full-state equation retains every quantum-reference
matrix block and records the actual path. The lexical layout and termination
loop are assembled separately; no high-level GCD operation is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Read the existing contents of an intrinsically writable cell. -/
def cellRead {shape : CShape} (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Divide the previous state word by the current divisor. -/
def divisionOp (first second : CWriteRef ctx (.unsignedWord width))
    (scratch : CWriteRef ctx (operandShape width)) :
    ClassicalOp (operandShape width) (operandShape width) ctx ctx :=
  .divRem width width ctx (.product (cellRead second) (cellRead first)) scratch

/-- Rotate the current divisor into the previous-word cell. -/
def rotateSecondOp (first second : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (cellRead first) second

/-- Copy the actually computed remainder into the current-word cell. -/
def takeRemainderOp (first : CWriteRef ctx (.unsignedWord width))
    (scratch : CWriteRef ctx (operandShape width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (.second (cellRead scratch)) first

/-- Compare the updated divisor with the internally initialized zero cell. -/
def testActiveOp (first : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit) :
    ClassicalOp (operandShape width) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product (cellRead first) zero) active

/-- Negate the actual comparison result to obtain the next branch condition. -/
def negateActiveOp (active : CWriteRef ctx .bit) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (cellRead active) active

/-- Literal five-instruction Euclidean update inside its division workspace. -/
def remainderBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (divisionOp first second scratch))
    (.seq (BitWord.instruction (execution := model) (rotateSecondOp first second))
      (.seq (BitWord.instruction (execution := model) (takeRemainderOp first scratch))
        (.seq (BitWord.instruction (execution := model) (testActiveOp first zero active))
          (BitWord.instruction (execution := model) (negateActiveOp active)))))

/-- The concrete store obtained from those same five atomic updates. -/
def remainderStore (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (divisionOp first second scratch)).applyOp
    (rotateSecondOp first second)).applyOp (takeRemainderOp first scratch)).applyOp
      (testActiveOp first zero active)).applyOp (negateActiveOp active)

/-- The actual native outputs determine the complete chronological instruction path. -/
def remainderStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) (store : Store ctx) :
    Store ctx × (remainderBody (model := model) first second zero active scratch).Path :=
  let divided := BitWord.instructionStep (execution := model) (divisionOp first second scratch)
    store
  let rotated := BitWord.instructionStep (execution := model) (rotateSecondOp first second)
    divided.1
  let taken := BitWord.instructionStep (execution := model) (takeRemainderOp first scratch)
    rotated.1
  let compared := BitWord.instructionStep (execution := model) (testActiveOp first zero active)
    taken.1
  let negated := BitWord.instructionStep (execution := model) (negateActiveOp active) compared.1
  (negated.1, (divided.2, (rotated.2, (taken.2, (compared.2, negated.2)))))

/-- The complete execution acts on the actual store and leaves every full quantum block intact. -/
theorem gcdRemainder_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (remainderBody (model := model) first second zero active scratch).execute Reference state =
      state.mapClassical (fun entry =>
        let result := remainderStep (model := model) first second zero active scratch entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [remainderBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Independent native event list of one genuine Euclidean update. -/
def remainderEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.divRem width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal
      width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- Every actual path emits exactly division, two copies, equality and negation. -/
theorem gcdRemainder_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody (model := model) first second zero active scratch).Path) :
    (remainderBody (model := model) first second zero active scratch).eventTrace path =
      remainderEvents model width := by
  change (BitWord.instruction (execution := model) (divisionOp first second scratch)).eventTrace
    path.1 ++ ((BitWord.instruction (execution := model) (rotateSecondOp first second)).eventTrace
      path.2.1 ++ ((BitWord.instruction (execution := model) (takeRemainderOp first
        scratch)).eventTrace
        path.2.2.1 ++ ((BitWord.instruction (execution := model) (testActiveOp first zero
          active)).eventTrace
          path.2.2.2.1 ++ (BitWord.instruction (execution := model) (negateActiveOp
            active)).eventTrace
            path.2.2.2.2))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual native ledger contains the same five explicit classical coordinates. -/
theorem gcdRemainder_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody (model := model) first second zero active scratch).Path) :
    (remainderBody (model := model) first second zero active scratch).resourcePool path =
      ResourcePool.ofList (remainderEvents model width) :=
  congrArg ResourcePool.ofList (gcdRemainder_eventTrace first second zero active scratch path)

/-- All five dependent classical instructions contribute serial unit-duration depth. -/
theorem gcdRemainder_unitDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody (model := model) first second zero active scratch).Path) :
    (remainderBody (model := model) first second zero active scratch).depth (fun _ => 1) path = 5
      := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
