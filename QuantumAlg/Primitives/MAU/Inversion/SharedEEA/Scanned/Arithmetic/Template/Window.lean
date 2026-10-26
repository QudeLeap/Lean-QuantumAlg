/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.NativeFold
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates

/-!
# Literal TTK placement on an original low work-word window

The source window is the actual low portion of Work2, and its target is
the matching portion of Work1. The complete physical complement remains
present. Translating most-significant-first operand coordinates to the
source's little-endian indices is a static gate placement, with no word
permutation added to the executed program [TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open EncodedBit NumberTheory.SharedEEA ArithmeticTemplate

private def lowIndex (width length : Nat) (fits : length ≤ width + 3) (index : Fin length) :
    Fin (width + 3) := ⟨length - 1 - index.val, by have := index.isLt; omega⟩

/-- Both operands are ordered lists of their literal existing physical positions. -/
def word (width length : Nat) (fits : length ≤ width + 3) (first : Bool) :
    Word (Scanned.encoding width) length where
  bit index := ArithmeticTemplate.wordBit width first (lowIndex width length fits index)

private lemma distinct (width length : Nat) (fits : length ≤ width + 3) (first : Bool)
    (left right : Fin length) (different : left ≠ right) :
    ((word width length fits first).bit left).wire ≠
      ((word width length fits first).bit right).wire := by
  apply word_distinct
  intro same
  apply different
  apply Fin.ext
  have values := congrArg Fin.val same
  change length - 1 - left.val = length - 1 - right.val at values
  have := left.isLt
  have := right.isLt
  omega

/-- Each selected operand bit has a distinct original position and a retained complement. -/
def placement (width length : Nat) (fits : length ≤ width + 3) :
    Addition.TTK.WordPlacement (Scanned.encoding width) length where
  addend := word width length fits false
  target := word width length fits true
  addendDistinct := by
    intro left right same
    by_contra different
    exact distinct width length fits false left right different same
  targetDistinct := by
    intro left right same
    by_contra different
    exact distinct width length fits true left right different same
  separate := fun left right =>
    (word_ne width (lowIndex width length fits right) (lowIndex width length fits left)).symm
  onto := Scanned.encoding_surjective width

private lemma source_onto (length : Nat) :
    Function.Surjective (Addition.TTK.encoding length).encode :=
  (prodEquiv (m := length) (n := length)).surjective

private lemma left_wire (length : Nat) (index : Fin length) :
    (Addition.TTK.leftBit length index).wire = Fin.castAdd length index.rev := by
  apply Fin.ext
  rw [Addition.TTK.ttkLeftBit_wire_val]
  change length - 1 - index.val = index.rev.val
  rw [Fin.val_rev]
  omega

private lemma right_wire (length : Nat) (index : Fin length) :
    (Addition.TTK.rightBit length index).wire = Fin.natAdd length index.rev := by
  apply Fin.ext
  rw [Addition.TTK.ttkRightBit_wire_val]
  change length + (length - 1 - index.val) = length + index.rev.val
  rw [Fin.val_rev]
  omega

private lemma original_index (width length : Nat) (fits : length ≤ width + 3)
    (index : Fin length) :
    lowIndex width length fits index.rev =
      (⟨index.val, lt_of_lt_of_le index.isLt fits⟩ : Fin (width + 3)) := by
  apply Fin.ext
  change length - 1 - index.rev.val = index.val
  rw [Fin.val_rev]
  have := index.isLt
  omega

/-- The literal TTK addend bit maps to exactly the source template's original Work2 position. -/
lemma placed_leftBit (width length : Nat) (fits : length ≤ width + 3) (index : Fin length) :
    ((placement width length fits).subsystem.placeBit (source_onto length)
      (Scanned.encoding_surjective width) (Addition.TTK.leftBit length index)) =
      ArithmeticTemplate.wordBit width false ⟨index.val, lt_of_lt_of_le index.isLt fits⟩ := by
  apply EncodedBit.eq_of_wire_eq
  rw [WireSubsystem.placeBit_wire, left_wire]
  change (wordPairSubsystem _ _ _ _ _).wires (Fin.castAdd length index.rev) = _
  rw [wordPairSubsystem_left]
  change (ArithmeticTemplate.wordBit width false (lowIndex width length fits index.rev)).wire = _
  rw [original_index]

/-- The literal TTK target bit maps to exactly the source template's original Work1 position. -/
lemma placed_rightBit (width length : Nat) (fits : length ≤ width + 3) (index : Fin length) :
    ((placement width length fits).subsystem.placeBit (source_onto length)
      (Scanned.encoding_surjective width) (Addition.TTK.rightBit length index)) =
      ArithmeticTemplate.wordBit width true ⟨index.val, lt_of_lt_of_le index.isLt fits⟩ := by
  apply EncodedBit.eq_of_wire_eq
  rw [WireSubsystem.placeBit_wire, right_wire]
  change (wordPairSubsystem _ _ _ _ _).wires (Fin.natAdd length index.rev) = _
  rw [wordPairSubsystem_right]
  change (ArithmeticTemplate.wordBit width true (lowIndex width length fits index.rev)).wire = _
  rw [original_index]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
