/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Util.Classical.OrderRecovery
import all QuantumAlg.Core.Execution.Store

/-!
# Actual input and result shapes for finite order recovery

The raw input keeps a borrowed modular-base encoding and measured phase bits
as distinct values. Canonicality and coprimality belong to the intrinsic source
input. The output contains exactly the optional candidate word of that source
specification; these encodings do not compute through a runtime reference.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

/-- Read the actual modular base and the original measured phase bits. -/
public abbrev inputShape (modulusWidth phaseBits : Nat) : CShape :=
  .product (.canonicalResidue modulusWidth) (.bits phaseBits)

/-- Every dyadic continued-fraction denominator fits the extra candidate bit. -/
public abbrev outputShape (phaseBits : Nat) : CShape :=
  .option (.unsignedWord (phaseBits + 1))

/-- Existing writable storage is read through its actual structural reference. -/
def cellRead {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- The mathematical source input's exact raw representation. -/
def encodeInput {modulusWidth phaseBits : Nat}
    {spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits}
    (input : ClassicalAlgorithms.OrderRecovery.Input spec) :
    CShape.Value (inputShape modulusWidth phaseBits) :=
  .product (.canonicalResidue input.base) (.bits input.terminalBits)

/-- Represent the source input by equality of the actual stored base and phase values. -/
def InputRepresents {modulusWidth phaseBits : Nat}
    {spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits}
    (actual : CShape.Value (inputShape modulusWidth phaseBits))
    (source : ClassicalAlgorithms.OrderRecovery.Input spec) : Prop :=
  actual = encodeInput source

/-- Encode precisely the optional finite word returned by intrinsic recovery. -/
def encodeOutput {phaseBits : Nat} : Option (Fin (2 ^ (phaseBits + 1))) →
    CShape.Value (outputShape phaseBits)
  | none => .optionNone
  | some word => .optionSome (.unsignedWord word)

/-- Read the actual nominal optional-word result without changing its represented value. -/
def decodeOutput {phaseBits : Nat} : CShape.Value (outputShape phaseBits) →
    Option (Fin (2 ^ (phaseBits + 1)))
  | .optionNone => none
  | .optionSome (.unsignedWord word) => some word

@[simp] theorem nativeRecovery_decode_encode {phaseBits : Nat}
    (output : Option (Fin (2 ^ (phaseBits + 1)))) :
    decodeOutput (encodeOutput output) = output := by
  cases output <;> rfl

@[simp] theorem nativeRecovery_encode_decode {phaseBits : Nat}
    (output : CShape.Value (outputShape phaseBits)) :
    encodeOutput (decodeOutput output) = output := by
  cases output with
  | optionNone => rfl
  | optionSome word => cases word; rfl

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
