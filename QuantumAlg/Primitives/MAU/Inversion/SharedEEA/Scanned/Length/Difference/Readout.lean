/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Frame
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag.Action
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Subtraction

/-! # Exact original pool readouts of the actual direct length difference and borrow -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Complete low subword of the original address or prefix, retaining every selected bit. -/
def value (width length : Nat) (prefixWord : Bool) (state : Data width) : BitVec length :=
  (if prefixWord then state.2.2.1 else state.2.1).extractLsb' 0 length

/-- Actual operand lenses read exactly their declared low subword, without a clean premise. -/
lemma word_get (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (prefixWord : Bool) (state : Data width) (position : Fin length) :
    ((word width length fits prefixWord).bit position).get state =
      (value width length prefixWord state).getMsbD position.val := by
  have within := position.isLt
  have sourceWithin : length - position.val ≤ ScanMetadata.addressWidth width := by omega
  have sourceIndex : ScanMetadata.addressWidth width - (length - position.val) =
      ScanMetadata.addressWidth width - length + position.val := by omega
  cases prefixWord <;>
    simp only [word, value, Bool.false_eq_true, if_false, if_true, index,
      addressBit_get, prefixBit_get, BitVec.getMsbD_extractLsb', Nat.zero_add, within,
      sourceWithin, sourceIndex, decide_true, Bool.true_and]

private lemma grouped_pair (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (state : Data width) :
    (((subsystem width length fits).full (source_onto length)
      (encoding_surjective width)).grouping state).1.1 =
        (((operands width length fits).subsystem.full
          Addition.TTK.WordPlacement.source_onto (encoding_surjective width)).grouping state).1 :=
  (operands width length fits).subsystem.withFlag_grouping_source (conjunctionBit width)
    (conjunction_separate width length fits) Addition.TTK.WordPlacement.source_onto
    (source_onto length) (encoding_surjective width) state

private lemma grouped_addend (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (state : Data width) :
    BitVec.ofFin ((((subsystem width length fits).full (source_onto length)
      (encoding_surjective width)).grouping state).1.1.1) = value width length false state := by
  rw [grouped_pair]
  exact (operands width length fits).grouped_addend state (value width length false state)
    (word_get width length fits false state)

private lemma grouped_target (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (state : Data width) :
    BitVec.ofFin ((((subsystem width length fits).full (source_onto length)
      (encoding_surjective width)).grouping state).1.1.2) = value width length true state := by
  rw [grouped_pair]
  exact (operands width length fits).grouped_target state (value width length true state)
    (word_get width length fits true state)

private lemma grouped_borrow (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (state : Data width) :
    (((subsystem width length fits).full (source_onto length)
      (encoding_surjective width)).grouping state).1.2 = state.2.2.2 :=
  (subsystem width length fits).full_source_read (source_onto length)
    (encoding_surjective width) (Addition.TTK.overflowBit length) (conjunctionBit width)
    (subsystem_borrow width length fits) state

private lemma target_location (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (position : Fin length) :
    (subsystem width length fits).wires
      (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.secondLens position)).wire =
        ((word width length fits true).bit position).wire := by
  have wire :
      (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.secondLens position)).wire =
        Fin.castAdd 1 (Addition.TTK.WordPlacement.secondLens position).wire := by
    apply Fin.ext
    rfl
  have lifted := subsystem_word width length fits
    (Addition.TTK.WordPlacement.secondLens position).wire
  have original : (operands width length fits).subsystem.wires
      (Addition.TTK.WordPlacement.secondLens position).wire =
        ((word width length fits true).bit position).wire :=
    wordPairSubsystem_right _ _ _ _ _ position
  exact (congrArg (subsystem width length fits).wires wire).trans (lifted.trans original)

/-- Each real prefix output bit contains the direct modular difference L-i. -/
lemma step_target_get (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) (position : Fin length) :
    ((word width length fits true).bit position).get (step width length fits state) =
      (value width length true state - value width length false state).getMsbD position.val := by
  have actual := (subsystem width length fits).full_step_source_read (source_onto length)
    (encoding_surjective width)
    (Addition.TTK.withOverflowBit (Addition.TTK.WordPlacement.secondLens position))
    ((word width length fits true).bit position) (target_location width length fits position)
    Addition.TTK.overflowSubtractionOutput state
  change ((word width length fits true).bit position).get (step width length fits state) =
    (BinaryLabelEncoding.finIdentityBit length position).get _ at actual
  rw [Addition.TTK.WordPlacement.fin_bit_get] at actual
  simp only [Addition.TTK.overflowSubtractionOutput] at actual
  rw [Addition.TTK.WordPlacement.subtraction_word, grouped_target, grouped_addend] at actual
  exact actual

/-- The real conjunction records precisely whether the original prefix is below the address. -/
lemma step_borrow (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) :
    (step width length fits state).2.2.2 = (state.2.2.2 ^^
      decide ((value width length true state).toNat < (value width length false state).toNat)) := by
  have actual := (subsystem width length fits).full_step_source_read (source_onto length)
    (encoding_surjective width) (Addition.TTK.overflowBit length) (conjunctionBit width)
    (subsystem_borrow width length fits) Addition.TTK.overflowSubtractionOutput state
  have left := congrArg BitVec.toNat (grouped_addend width length fits state)
  have right := congrArg BitVec.toNat (grouped_target width length fits state)
  change ((((subsystem width length fits).full (source_onto length)
    (encoding_surjective width)).grouping state).1.1.1).val =
      (value width length false state).toNat at left
  change ((((subsystem width length fits).full (source_onto length)
    (encoding_surjective width)).grouping state).1.1.2).val =
      (value width length true state).toNat at right
  change (step width length fits state).2.2.2 =
    ((((subsystem width length fits).full (source_onto length)
      (encoding_surjective width)).grouping state).1.2 ^^
      decide (((((subsystem width length fits).full (source_onto length)
        (encoding_surjective width)).grouping state).1.1.2).val <
        ((((subsystem width length fits).full (source_onto length)
          (encoding_surjective width)).grouping state).1.1.1).val)) at actual
  rw [grouped_borrow, left, right] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
