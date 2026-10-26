/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Clean
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address

/-!
# Full metadata-address unary selector on the original EEA frame

The address retains its full carry width in most-significant-first order.
The existing source Ctrl is the root enable, and the ten P-256 prefix wires
are exactly the prefix word of the shared pool. No address bit is truncated,
measured or copied to an unaccounted register.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionFrame

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- The original source control supplies the traversal's existing root enable. -/
def enable (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (SharedEEA.controlBit width)

/-- Position zero is the original Ctrl; the remaining positions are the complete prefix word. -/
def stack (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1)) :
    EncodedBit (encoding width) :=
  if zero : index.val = 0 then enable width
  else prefixBit width ⟨index.val - 1, by have := index.isLt; omega⟩

private lemma stack_distinct (width : Nat) :
    Function.Injective (fun index => (stack width index).wire) := by
  intro left right same
  dsimp only [stack] at same
  split_ifs at same with first second
  · exact Fin.ext (first.trans second.symm)
  · exact False.elim (source_prefix_ne width _ _ same)
  · exact False.elim ((source_prefix_ne width _ _).symm same)
  · apply Fin.ext
    have equal := congrArg Fin.val same
    simp only [prefixBit_wire] at equal
    omega

private lemma separate (width : Nat) (addressIndex : Fin (ScanMetadata.addressWidth width))
    (stackIndex : Fin (ScanMetadata.addressWidth width + 1)) :
    (addressBit width addressIndex).wire ≠ (stack width stackIndex).wire := by
  unfold stack
  split
  · exact (source_address_ne width _ addressIndex).symm
  · exact address_prefix_ne width addressIndex _

/-- The certified actual frame uses all original full-carry address and prefix positions. -/
def frame (width : Nat) : SelectorFrame (encoding width) (ScanMetadata.addressWidth width) where
  address := addressBit width
  stack := stack width
  addressDistinct := by
    intro left right same
    by_contra different
    exact address_address_ne width left right different same
  stackDistinct := stack_distinct width
  separate := separate width

/-- Every address bit is the corresponding original most-significant-first physical bit. -/
lemma address_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width))
    (state : Data width) :
    ((frame width).address index).get state = state.2.1.getMsbD index.val :=
  addressBit_get width index state

/-- The traversal reads the original source control and the actual full prefix word. -/
lemma stack_get (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1))
    (state : Data width) :
    ((frame width).stack index).get state =
      if index.val = 0 then state.1.control else state.2.2.1.getMsbD (index.val - 1) := by
  change (stack width index).get state = _
  unfold stack
  split_ifs
  · rfl
  · exact prefixBit_get width _ state

/-- The real zero prefix word is precisely the clean workspace required by the traversal. -/
lemma clean_of_prefix_zero (width : Nat) (state : Data width)
    (zero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (frame width).CleanFrom 0 state := by
  intro index _present
  rw [stack_get]
  have nonzero : index.succ.val ≠ 0 := by change index.val + 1 ≠ 0; omega
  rw [if_neg nonzero, zero, BitVec.getMsbD_zero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionFrame
