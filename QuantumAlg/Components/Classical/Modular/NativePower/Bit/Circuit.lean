/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Placement

/-!
# Actual MSB-first square-and-multiply circuit

Each step squares the current accumulator through full-product reduction and
then reads an actual stored exponent bit. Only a true bit selects a second
full-product reduction with the stored base. The finite list contains the
exponent's declared structural bit references, including leading zero slots.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The base multiplication selected by one actual stored Boolean result. -/
def multiplyChoice (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then scopedMultiply (wordRead output) base modulus output else .id ctx

/-- Square the actual accumulator and then read the exponent bit to select multiplication. -/
def bitCircuit (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit) : Circuit ctx ctx :=
  .seq (scopedMultiply (wordRead output) (wordRead output) modulus output)
    (.branch bit (multiplyChoice base modulus output))

/-- Compose precisely the supplied finite list of actual exponent-bit references. -/
def foldBits (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : List (CInputRef ctx .bit) → Circuit ctx ctx
  | [] => .id ctx
  | bit :: rest => .seq (bitCircuit base modulus output bit) (foldBits base modulus output rest)

/-- Visit every declared exponent slot in its existing most-significant-bit-first order. -/
def exponentCircuit {exponentWidth : Nat} (base : CInputRef ctx (.unsignedWord width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  foldBits base modulus output
    (List.ofFn (fun index : Fin exponentWidth => CInputRef.wordBitGet exponent index))

end QuantumAlg.ClassicalRoutines.Modular.NativePower
