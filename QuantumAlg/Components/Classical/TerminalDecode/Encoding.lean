/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Classical.TerminalDecode
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Util.Classical.TerminalDecode
import all QuantumAlg.Core.Execution.Store

/-!
# Typed terminal bits and materialized unsigned words

The pure decoder fixes the bit order and exact width. A runtime source consists
of actual stored bit references; reconstructing their mathematical value here
is a specification. The circuit owner performs the corresponding shift and
conditional increment instructions before writing an unsigned result.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open ClassicalAlgorithms.TerminalDecode

/-- Exactly the statically known number of terminal bits. -/
public abbrev InputShape (width : Nat) : CShape := .bits width

/-- Materialized unsigned output with the same width. -/
public abbrev OutputShape (width : Nat) : CShape := .unsignedWord width

/-- Read the actual cell named by a writable reference. -/
def writeInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (output : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage output.toCStorageRef

/-- Interpret the input bit order without altering its fixed shape. -/
def decodeInput {width : Nat} (order : BitOrder) :
    CShape.Value (InputShape width) → Input width
  | .bits bits => ⟨order, bits⟩

/-- Exact input representation at the intrinsic word boundary. -/
def InputRepresents {width : Nat} (order : BitOrder)
    (encoded : CShape.Value (InputShape width)) (semantic : Input width) : Prop :=
  decodeInput order encoded = semantic

/-- Read the already materialized output as the intrinsic bounded word. -/
def decodeOutput {width : Nat} : CShape.Value (OutputShape width) → Output width
  | .unsignedWord word => ⟨word.val, word.isLt⟩

/-- The concrete output contains precisely the pure decoder result. -/
def OutputRepresents {width : Nat}
    (encoded : CShape.Value (OutputShape width)) (semantic : Output width) : Prop :=
  decodeOutput encoded = semantic

/-- The two unsigned encodings agree on their actual natural projection. -/
theorem terminalDecode_decodeOutput_val {width : Nat}
    (encoded : CShape.Value (OutputShape width)) :
    (decodeOutput encoded).val = encoded.toNat := by
  cases encoded
  rfl

/-- The source input is tied to the current real store and structural bit reads. -/
def decodeInputFromBitRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (order : BitOrder) (store : Execution.Store ctx)
    (inputs : Fin width → CInputRef ctx .bit) : Input width :=
  ⟨order, fun bit => (store.read (inputs bit)).toBool⟩

/-- Shift-and-append consumes little-endian sources in reverse order. -/
def sourceIndex {width : Nat} (order : BitOrder) (index : Fin width) : Fin width :=
  match order with
  | .bigEndian => index
  | .littleEndian => index.rev

/-- Address selection agrees exactly with the pure accumulator order. -/
theorem terminalDecode_sourceIndex_accumulatorBits {width : Nat}
    (order : BitOrder) (bits : Fin width → Bool) (index : Fin width) :
    bits (sourceIndex order index) = accumulatorBits order bits index := by
  cases order <;> rfl

end QuantumAlg.ClassicalRoutines.TerminalDecode
