/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual native saturating subtraction

A real comparison selects one of two existing word instructions: self-XOR
clears the output on underflow, and ordinary wrapping subtraction computes
the difference otherwise. The comparison flag is a single actual fresh
lexical bit and is released by the same scope. The caller provides only
two structural operand reads and one writable output, which may alias
an operand. No new opcode or initialized caller workspace is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The one actual fresh decision cell used before the output instruction. -/
def context (ctx : RuntimeCtx kind) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- Intrinsic reference to the real decision head. -/
def decision (ctx : RuntimeCtx kind) : CWriteRef (context ctx) .bit :=
  .workspaceHead ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- An original operand read lifted under the actual decision bit. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) : CInputRef (context ctx) shape :=
  input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The original writable destination beneath the same real flag. -/
def underWrite {shape : CShape} (output : CWriteRef ctx shape) : CWriteRef (context ctx) shape :=
  output.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh

/-- The actual pre-output comparison asks whether unsigned subtraction would underflow. -/
def compareOp (left right : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit
      (context ctx) (context ctx) :=
  .wordBinary .lessThan width (context ctx)
    (.product (underRead left) (underRead right)) (decision ctx)

/-- The underflow arm clears the real output with its actual self-XOR instruction. -/
def clearOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) (.unsignedWord width)
      (context ctx) (context ctx) :=
  let target := underRead (.storage output.toCStorageRef)
  .wordBinary .bitXor width (context ctx) (.product target target) (underWrite output)

/-- The other arm uses the real word subtraction on both original operands. -/
def subtractOp (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) (.unsignedWord width)
      (context ctx) (context ctx) :=
  .wordBinary .sub width (context ctx)
    (.product (underRead left) (underRead right)) (underWrite output)

/-- Closed native bodies selected by the actual stored underflow flag. -/
def selected (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    CShape.Value .bit → Circuit (context ctx) (context ctx)
  | .bit true => .classical (clearOp output)
  | .bit false => .classical (subtractOp left right output)

/-- Real comparison followed by its stored-result branch. -/
def body (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit (context ctx) (context ctx) :=
  .seq (.classical (compareOp left right))
    (.branch (.storage (decision ctx).toCStorageRef) (selected left right output))

/-- Full native saturating subtraction with one owned and released classical flag. -/
def into (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh (body left right output)

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
