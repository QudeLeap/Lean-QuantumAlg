/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Store

/-!
# Literal native loading of a known word

The constant is a compilation parameter. Each bit contributes one real word
shift followed by a compile-selected increment or identity. No runtime
callback, constant-storage cell, or extra classical opcode is introduced.
Exactly the target width's bits are consumed in most-significant-bit order.
-/

namespace QuantumAlg.ClassicalRoutines.ConstantWord

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Read the actual target cell before overwriting it. -/
def targetRead (output : CWriteRef ctx (.unsignedWord width)) :
    CInputRef ctx (.unsignedWord width) := .storage output.toCStorageRef

/-- The actual truncating shift used for one compiled bit. -/
def shiftOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftLeft width ctx (targetRead output) output

/-- The actual wrapping increment emitted only for a compiled one bit. -/
def incrementOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .increment width ctx (targetRead output) output

/-- Append one compilation-time bit with its real selected native instructions. -/
def append (output : CWriteRef ctx (.unsignedWord width)) : Bool → Circuit ctx ctx
  | false => .seq (.classical (shiftOp output)) (.id ctx)
  | true => .seq (.classical (shiftOp output)) (.classical (incrementOp output))

/-- Literal sequential composition of all supplied compilation-time bits. -/
def fold (output : CWriteRef ctx (.unsignedWord width)) : List Bool → Circuit ctx ctx
  | [] => .id ctx
  | bit :: remaining => .seq (append output bit) (fold output remaining)

/-- The compilation-time bits in the order consumed by the actual shifts. -/
def constantBits (width constant : Nat) : Fin width → Bool :=
  fun index => constant.testBit index.rev.val

/-- Load a constant modulo the intrinsic target-word width using the literal native fold. -/
def circuit (output : CWriteRef ctx (.unsignedWord width)) (constant : Nat) : Circuit ctx ctx :=
  fold output (List.ofFn (constantBits width constant))

end QuantumAlg.ClassicalRoutines.ConstantWord
