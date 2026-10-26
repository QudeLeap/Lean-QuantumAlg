/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Circuit

/-!
# Actual lookup and measurement-unlookup on the same supplied result word

The lookup target is the original unlookup result word. Both source-table
halves and the paid split feedback read the same table, with low addresses
occupying the least significant positions. All quantum systems are supplied
existing positions; the complete composed circuit forbids allocation.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

/-- Join the original low and high address values without truncating either field. -/
def joinedAddress {highWidth lowWidth : Nat}
    (high : Fin (2 ^ highWidth)) (low : Fin (2 ^ lowWidth)) :
    Fin (2 ^ (highWidth + lowWidth)) :=
  Fin.cast (pow_add 2 highWidth lowWidth).symm (finProdFinEquiv (high, low))

/-- The original low address is the least significant part of the joined address. -/
lemma joinedAddress_val {highWidth lowWidth : Nat}
    (high : Fin (2 ^ highWidth)) (low : Fin (2 ^ lowWidth)) :
    (joinedAddress high low).val = low.val + 2 ^ lowWidth * high.val := rfl

/-- The actual paid split feedback uses exactly the same full source table. -/
def splitTable {highWidth lowWidth wordWidth : Nat}
    (table : Bool → Fin (2 ^ (highWidth + lowWidth)) → Fin (2 ^ wordWidth))
    (top : Bool) (high : Fin (2 ^ highWidth)) (low : Fin (2 ^ lowWidth)) :
    Fin (2 ^ wordWidth) := table top (joinedAddress high low)

namespace UnlookupFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}

/-- The actual lookup targets the same existing systems that are subsequently measured and reset. -/
def cycleTarget (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (lookup : SelectorFrame encoding (highRemaining + lowWidth))
    (outsideAddress : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.address index).wire)
    (outsideStack : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.stack index).wire) :
    LookupTarget lookup resultWidth where
  word := frame.result
  distinct := frame.resultDistinct
  outsideAddress := outsideAddress
  outsideStack := outsideStack

/-- A complete actual load/unlookup pair, including physical result reset
and paid split feedback. -/
def cycleCircuit (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)
    (lookup : SelectorFrame encoding (highRemaining + lowWidth))
    (outsideAddress : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.address index).wire)
    (outsideStack : ∀ bit index,
      (frame.result.bit bit).wire ≠ (lookup.stack index).wire)
    (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (table : Bool → Fin (2 ^ (highRemaining + lowWidth)) → Fin (2 ^ resultWidth))
    (height : Nat) (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  (SelectorFrame.placedCircuit physical sameWires
    (splitLookupProgram lookup physical .empty
      (frame.cycleTarget lookup outsideAddress outsideStack) table height)).seq
    (frame.circuit physical sameWires output mask parity (splitTable table))

end UnlookupFrame

end

end QuantumAlg.EncodedBit.WindowLookup
