/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Append
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Compose
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.WordPair
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates

/-!
# Complete static coordinates of both original rotated work words

The public displacement defines a mathematical full-frame certificate,
with every metadata, flag and physical pool position in its retained
complement. It supplies no executed permutation: the actual paid
quantum-metadata barrel and its cleanup require separate realization.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed

noncomputable section

open EncodedBit

private lemma word_injective (width : Nat) (first : Bool) :
    Function.Injective (fun index => (ArithmeticRotation.bit width first index).wire) := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
  omega

private lemma words_separate (width : Nat) (left right : Fin (width + 3)) :
    (ArithmeticRotation.bit width true left).wire ≠
      (ArithmeticRotation.bit width false right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [ArithmeticRotation.bit_value, ArithmeticRotation.bit_value] at values
  have within := left.isLt
  simp only [if_true, Bool.false_eq_true, if_false, zero_add] at values
  omega

/-- Both original physical words have their unchanged most-significant-first coordinate order. -/
def operands (width : Nat) :
    WireSubsystem (Addition.TTK.encoding (width + 3)) (encoding width) :=
  wordPairSubsystem ⟨ArithmeticRotation.bit width true⟩ ⟨ArithmeticRotation.bit width false⟩
    (word_injective width true) (word_injective width false) (words_separate width)

/-- All remaining original physical positions form the explicit complete retained complement. -/
def operandsFrame (width : Nat) :
    FullPlacement (BinaryLabelEncoding.prod (Addition.TTK.encoding (width + 3))
      (BinaryLabelEncoding.finIdentity (operands width).complementWidth)) (encoding width) :=
  (operands width).full (ArithmeticWindow.source_onto (width + 3))
    (Scanned.encoding_surjective width)

/-- Both whole words use the same public static inverse-rotation displacement. -/
def pairPermutation (width displacement : Nat) :
    Equiv.Perm (Fin (Addition.TTK.encoding (width + 3)).width) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (permutation width ^ displacement) (permutation width ^ displacement)).trans
      finSumFinEquiv)

/-- Complete pair coordinates are derived from those same literal physical wire positions. -/
def pairFrame (width displacement : Nat) :=
  FullPlacement.ofWires (Addition.TTK.encoding (width + 3))
    (Addition.TTK.encoding (width + 3)) (ArithmeticWindow.source_onto (width + 3))
    (ArithmeticWindow.source_onto (width + 3)) (pairPermutation width displacement)

/-- Restore the original field grouping around the statically rotated complete operand pair. -/
def frame (width displacement : Nat) : FullPlacement (encoding width) (encoding width) :=
  ((operandsFrame width).inverse.compose
    ((pairFrame width displacement).appendRight
      (BinaryLabelEncoding.finIdentity (operands width).complementWidth))).compose
        (operandsFrame width)

/-- The complete static frame rotates only the two full original work words. -/
lemma frame_grouping (width displacement : Nat) (state : Data width) :
    (frame width displacement).grouping state =
      (operandsFrame width).grouping.symm
        ((pairFrame width displacement).grouping ((operandsFrame width).grouping state).1,
          ((operandsFrame width).grouping state).2) := rfl

/-- Every original pair coordinate is moved by exactly the same declared physical permutation. -/
lemma frame_mapped_operand (width displacement : Nat)
    (index : Fin (Addition.TTK.encoding (width + 3)).width) :
    (frame width displacement).mappedWire
        ((operandsFrame width).mappedWire (Fin.castAdd (operands width).complementWidth index)) =
      (operandsFrame width).mappedWire
        (Fin.castAdd (operands width).complementWidth
          (pairPermutation width displacement index)) := by
  rw [frame, FullPlacement.compose_mappedWire, FullPlacement.compose_mappedWire,
    FullPlacement.inverse_mappedWire]
  have restore : (operandsFrame width).wireEquiv.symm
      ((operandsFrame width).mappedWire (Fin.castAdd (operands width).complementWidth index)) =
        Fin.castAdd (operands width).complementWidth index :=
    (operandsFrame width).wireEquiv.symm_apply_apply _
  rw [restore]
  have appended := FullPlacement.appendRight_mappedWire_source
    (pairFrame width displacement)
    (BinaryLabelEncoding.finIdentity (operands width).complementWidth) index
  have position : (pairFrame width displacement).mappedWire index =
      pairPermutation width displacement index := by
    apply Fin.ext
    change FullPlacement.wireAddress _ _ (pairPermutation width displacement) index.val = _
    exact dif_pos index.isLt
  exact (congrArg (operandsFrame width).mappedWire appended).trans
    (congrArg (fun selected => (operandsFrame width).mappedWire
      (Fin.castAdd (operands width).complementWidth selected)) position)

/-- Every original saved coordinate, including the whole physical pool, stays at its own wire. -/
lemma frame_mapped_complement (width displacement : Nat)
    (index : Fin (operands width).complementWidth) :
    (frame width displacement).mappedWire
        ((operandsFrame width).mappedWire
          (Fin.natAdd (Addition.TTK.encoding (width + 3)).width index)) =
      (operandsFrame width).mappedWire
        (Fin.natAdd (Addition.TTK.encoding (width + 3)).width index) := by
  rw [frame, FullPlacement.compose_mappedWire, FullPlacement.compose_mappedWire,
    FullPlacement.inverse_mappedWire]
  have restore : (operandsFrame width).wireEquiv.symm
      ((operandsFrame width).mappedWire
        (Fin.natAdd (Addition.TTK.encoding (width + 3)).width index)) =
        Fin.natAdd (Addition.TTK.encoding (width + 3)).width index :=
    (operandsFrame width).wireEquiv.symm_apply_apply _
  rw [restore, FullPlacement.appendRight_mappedWire_extra]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed
