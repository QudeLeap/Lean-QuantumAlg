/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Range
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates
import all QuantumAlg.Components.Encoded.BitGates.StateEquality

/-! # Literal whole-word and retained physical positions of the complete static rotation frame -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed

noncomputable section

open EncodedBit

private lemma operand_prefix (width : Nat) (index : Fin (Addition.TTK.encoding (width + 3)).width) :
    (operandsFrame width).mappedWire (Fin.castAdd (operands width).complementWidth index) =
      (operands width).wires index := by
  have actual := (operands width).placeBit_wire (ArithmeticWindow.source_onto (width + 3))
    (Scanned.encoding_surjective width) (fullBit (ArithmeticWindow.source_onto (width + 3)) index)
  exact actual

private lemma word_prefix (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (operandsFrame width).mappedWire
        (Fin.castAdd (operands width).complementWidth (pairBit width first index).wire) =
      (ArithmeticRotation.bit width first index).wire :=
  (operand_prefix width _).trans (operand_location width first index)

/-- Every whole-word source position is moved to its exact declared original physical wire. -/
lemma frame_mapped_word (width displacement : Nat) (first : Bool) (index : Fin (width + 3)) :
    (frame width displacement).mappedWire (ArithmeticRotation.bit width first index).wire =
      (ArithmeticRotation.bit width first ((permutation width ^ displacement) index)).wire := by
  have actual := frame_mapped_operand width displacement (pairBit width first index).wire
  rw [word_prefix, pairPermutation_bit, word_prefix] at actual
  exact actual

/-- Every physical position outside the two original full words stays at its own original wire. -/
lemma frame_mapped_other (width displacement : Nat) (observed : Fin (encoding width).width)
    (outside : observed ∉ Set.range (operands width).wires) :
    (frame width displacement).mappedWire observed = observed := by
  obtain ⟨wire, location⟩ := (operandsFrame width).wire_surjective observed
  change (operandsFrame width).mappedWire wire = observed at location
  obtain ⟨selected, rfl⟩ := finSumFinEquiv.surjective wire
  cases selected with
  | inl index =>
      have original := (operand_prefix width index).symm.trans location
      exact False.elim (outside ⟨index, original⟩)
  | inr index =>
      change (operandsFrame width).mappedWire
        (Fin.natAdd (Addition.TTK.encoding (width + 3)).width index) = observed at location
      have actual := frame_mapped_complement width displacement index
      rw [location] at actual
      exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed
