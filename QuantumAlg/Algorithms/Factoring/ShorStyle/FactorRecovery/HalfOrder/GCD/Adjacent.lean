/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual adjacent half-power words for the two factor GCDs

The stored half-power residue is widened by one bit before either adjacent
word is formed. The successor therefore cannot overflow. For the predecessor,
the actual wrapping decrement sets the new highest bit exactly when the old
word was zero. That stored bit selects one real self-XOR to restore zero,
matching natural subtraction at zero without a host arithmetic callback.

The left and right GCD calls use the same construction with a compile-time
choice of direction. No additional classical or quantum workspace is needed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual widened cell used by the adjacent-word arithmetic. -/
def read (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    CInputRef ctx (.unsignedWord (width + 1)) := .storage output.toCStorageRef

/-- The real widening instruction preserves all bits of the stored half-power. -/
def resizeOp (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx input output

/-- Compile the selected adjacent direction into one existing native word instruction. -/
def adjacentOp (successor : Bool) (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.unsignedWord (width + 1)) (.unsignedWord (width + 1)) ctx ctx :=
  .wordUnary (if successor then .increment else .decrement) (width + 1) ctx (read output) output

/-- A genuine native self-XOR clears the underflow word when that arm is selected. -/
def clearOp (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.unsignedWord (width + 1)) ctx ctx :=
  .wordBinary .bitXor (width + 1) ctx (.product (read output) (read output)) output

/-- The newly available highest bit is read structurally from the actual widened word. -/
def highBit (output : CWriteRef ctx (.unsignedWord (width + 1))) : CInputRef ctx .bit :=
  .wordBitGet (read output) 0

/-- Only the real underflow arm emits the clearing instruction. -/
def trimArm (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => .classical (clearOp output)

/-- Read the stored underflow bit and execute exactly its selected arm. -/
def trim (output : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .branch (highBit output) (trimArm output)

/-- The successor is one operation; the predecessor additionally trims actual underflow. -/
def tail (successor : Bool) (output : CWriteRef ctx (.unsignedWord (width + 1))) :
    Circuit ctx ctx :=
  if successor then .classical (adjacentOp true output)
  else .seq (.classical (adjacentOp false output)) (trim output)

/-- The actual widening and selected adjacent-word arithmetic share the same written cell. -/
def code (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit ctx ctx :=
  .seq (.classical (resizeOp input output)) (tail successor output)

/-- Every actual adjacent-word path contains the widening instruction first. -/
theorem code_eventTrace (successor : Bool) (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord (width + 1)))
    (path : (code successor input output).Path) :
    (code successor input output).eventTrace path =
      Resource.Event.classicalOperation (.wordResize width (width + 1)) ::
        (tail successor output).eventTrace path.2 := rfl

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeAdjacentWord
