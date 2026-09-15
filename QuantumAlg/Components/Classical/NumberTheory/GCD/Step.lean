/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Encoding
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace

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
def remainderBody (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) : Circuit ctx ctx :=
  .seq (.classical (divisionOp first second scratch))
    (.seq (.classical (rotateSecondOp first second))
      (.seq (.classical (takeRemainderOp first scratch))
        (.seq (.classical (testActiveOp first zero active))
          (.classical (negateActiveOp active)))))

/-- The concrete store obtained from those same five atomic updates. -/
def remainderStore (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (divisionOp first second scratch)).applyOp
    (rotateSecondOp first second)).applyOp (takeRemainderOp first scratch)).applyOp
      (testActiveOp first zero active)).applyOp (negateActiveOp active)

/-- The complete execution acts on the actual store and leaves every full quantum block intact. -/
theorem gcdRemainder_execute (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (remainderBody first second zero active scratch).execute Reference state =
      state.mapClassical (fun entry =>
        (remainderStore first second zero active scratch entry.1,
          (entry.2, ((), ((), ((), ((), ()))))))) := by
  simp only [remainderBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Independent native event list of one genuine Euclidean update. -/
def remainderEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.divRem width width),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordBinary .equal width),
    .classicalOperation (.bit .not)]

/-- Every actual path emits exactly division, two copies, equality and negation. -/
theorem gcdRemainder_eventTrace (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody first second zero active scratch).Path) :
    (remainderBody first second zero active scratch).eventTrace path =
      remainderEvents kind width := rfl

/-- The actual native ledger contains the same five explicit classical coordinates. -/
theorem gcdRemainder_resourcePool (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody first second zero active scratch).Path) :
    (remainderBody first second zero active scratch).resourcePool path =
      ResourcePool.ofList (remainderEvents kind width) := rfl

/-- All five dependent classical instructions contribute serial unit-duration depth. -/
theorem gcdRemainder_unitDepth (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (scratch : CWriteRef ctx (operandShape width))
    (path : (remainderBody first second zero active scratch).Path) :
    (remainderBody first second zero active scratch).depth (fun _ => 1) path = 5 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
