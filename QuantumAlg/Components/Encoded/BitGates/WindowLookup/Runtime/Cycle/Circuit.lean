/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Lookup
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Unlookup.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Circuit

/-!
# Actual runtime-array lookup and paid measurement unlookup

The native loader and every paid feedback row read the same supplied array
through structural references. Original low and high address positions are
joined without truncation. The original result systems are measured, reset,
reused for unary feedback and restored by the actual native inverse.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {wordWidth lowWidth highRemaining : Nat}

/-- Every high/low feedback word is read from the same actual complete classical table array. -/
def splitInputs (source : CInputRef ctx
    (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (top : Bool) (high : Fin (2 ^ highRemaining)) (low : Fin (2 ^ lowWidth)) :
    CInputRef ctx (.unsignedWord wordWidth) :=
  .vectorGet source (index top (joinedAddress high low))

/-- The actual runtime load/unlookup pair retains all native AND/XOR, feedback and reset leaves. -/
def cycleCircuit (frame : UnlookupFrame encoding wordWidth lowWidth highRemaining)
    (lookup : SelectorFrame encoding (highRemaining + lowWidth))
    (outsideAddress : ∀ bit label,
      (frame.result.bit bit).wire ≠ (lookup.address label).wire)
    (outsideStack : ∀ bit label,
      (frame.result.bit bit).wire ≠ (lookup.stack label).wire)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (source : CInputRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (height : Nat) (output : Fin wordWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits wordWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (lookupCircuit source lookup (frame.cycleTarget lookup outsideAddress outsideStack)
    physical sameWires height).seq
      (RuntimeUnlookup.circuit frame physical sameWires output mask parity temporary
        (splitInputs source))

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
