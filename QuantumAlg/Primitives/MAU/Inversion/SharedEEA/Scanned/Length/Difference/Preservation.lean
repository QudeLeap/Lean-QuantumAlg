/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Frame
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement

/-! # Complete original-source and high-flag preservation of the actual length difference -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma outside_subsystem (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (observed : EncodedBit (encoding width))
    (addressOutside : ∀ position,
      (addressBit width (index width length fits position)).wire ≠ observed.wire)
    (prefixOutside : ∀ position,
      (prefixBit width (index width length fits position)).wire ≠ observed.wire)
    (borrowOutside : (conjunctionBit width).wire ≠ observed.wire) :
    observed.wire ∉ Set.range (subsystem width length fits).wires := by
  rintro ⟨selected, same⟩
  have outside : ∀ selected, (subsystem width length fits).wires selected ≠ observed.wire := by
    intro selected
    refine Fin.addCases (m := (Addition.TTK.encoding length).width) (n := 1)
      (fun ordinary => ?_) (fun flag => ?_) selected
    · rw [subsystem_word]
      change (wordPairSubsystem _ _ _ _ _).wires ordinary ≠ observed.wire
      refine Fin.addCases (m := length) (n := length)
        (fun source => ?_) (fun target => ?_) ordinary
      · rw [wordPairSubsystem_left]
        exact addressOutside source
      · rw [wordPairSubsystem_right]
        exact prefixOutside target
    · have zero : flag = (0 : Fin 1) := Subsingleton.elim _ _
      subst flag
      exact fun same => borrowOutside ((subsystem_borrow width length fits).symm.trans same)
  exact outside selected same

/-- Every real source outside the two selected low operands and borrow remains unchanged. -/
lemma step_get_of_outside (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (state : Data width)
    (observed : EncodedBit (encoding width))
    (addressOutside : ∀ position,
      (addressBit width (index width length fits position)).wire ≠ observed.wire)
    (prefixOutside : ∀ position,
      (prefixBit width (index width length fits position)).wire ≠ observed.wire)
    (borrowOutside : (conjunctionBit width).wire ≠ observed.wire) :
    observed.get (step width length fits state) = observed.get state :=
  (subsystem width length fits).full_step_other_read (source_onto length)
    (encoding_surjective width) observed
    (outside_subsystem width length fits observed addressOutside prefixOutside borrowOutside)
    Addition.TTK.overflowSubtractionOutput state

/-- The complete original register frame is physically disjoint from this actual pool arithmetic. -/
lemma step_original (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) (observed : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width observed).get (step width length fits state) =
      (sourceBit width observed).get state :=
  step_get_of_outside width length fits state (sourceBit width observed)
    (fun position => (source_address_ne width observed (index width length fits position)).symm)
    (fun position => (source_prefix_ne width observed (index width length fits position)).symm)
    (source_conjunction_ne width observed).symm

private lemma source_location (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (position : Fin length) :
    (subsystem width length fits).wires
      (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.firstLens position)).wire =
        ((word width length fits false).bit position).wire := by
  have wire :
      (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.firstLens position)).wire =
        Fin.castAdd 1 (Addition.TTK.WordPlacement.firstLens position).wire := by
    apply Fin.ext
    rfl
  have lifted := subsystem_word width length fits
    (Addition.TTK.WordPlacement.firstLens position).wire
  have original : (operands width length fits).subsystem.wires
      (Addition.TTK.WordPlacement.firstLens position).wire =
        ((word width length fits false).bit position).wire :=
    wordPairSubsystem_left _ _ _ _ _ position
  exact (congrArg (subsystem width length fits).wires wire).trans (lifted.trans original)

/-- Each actual subtrahend bit is restored even on arbitrary initial borrow and output labels. -/
lemma step_addend_get (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) (position : Fin length) :
    ((word width length fits false).bit position).get (step width length fits state) =
      ((word width length fits false).bit position).get state := by
  have actual := (subsystem width length fits).full_step_source_read (source_onto length)
    (encoding_surjective width)
    (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.firstLens position))
    ((word width length fits false).bit position) (source_location width length fits position)
    Addition.TTK.overflowSubtractionOutput state
  change ((word width length fits false).bit position).get (step width length fits state) =
    (BinaryLabelEncoding.finIdentityBit length position).get _ at actual
  rw [Addition.TTK.WordPlacement.fin_bit_get] at actual
  simp only [Addition.TTK.overflowSubtractionOutput, Addition.TTK.subtractionOutput] at actual
  rw [grouped_addend] at actual
  exact actual.trans (word_get width length fits false state position).symm

/-- The full selected target has the exact finite difference, independently of high flags. -/
lemma step_value (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) :
    value width length true (step width length fits state) =
      value width length true state - value width length false state := by
  apply BitVec.eq_of_getMsbD_eq
  intro position within
  rw [← word_get width length fits true _ ⟨position, within⟩]
  exact step_target_get width length fits state ⟨position, within⟩

/-- A high prefix bit is outside the low subtraction and retains its validity information. -/
lemma step_high_prefix (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (strict : length < ScanMetadata.addressWidth width) (state : Data width) :
    (prefixBit width ⟨0, by omega⟩).get (step width length fits state) =
      (prefixBit width ⟨0, by omega⟩).get state := by
  apply step_get_of_outside
  · intro position
    exact address_prefix_ne width _ _
  · intro position
    apply prefix_prefix_ne
    intro same
    have values := congrArg Fin.val same
    change ScanMetadata.addressWidth width - length + position.val = 0 at values
    omega
  · exact (prefix_conjunction_ne width _).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
