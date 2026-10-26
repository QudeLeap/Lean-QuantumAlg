/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag

/-!
# Exact physical operands for direct clipped length subtraction

Only a public low subword of the existing address and prefix participates.
The original conjunction is the actual borrow output. Every unselected high
address or prefix position remains in the complete physical complement.
This includes the active and validity flags used by the P-256 consumer.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Static low-subword coordinates retain the declared most-significant-first order. -/
def index (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (position : Fin length) : Fin (ScanMetadata.addressWidth width) :=
  ⟨ScanMetadata.addressWidth width - length + position.val, by
    have within := position.isLt
    omega⟩

/-- Both actual operands are existing pool subwords; the prefix is the difference target. -/
def word (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (prefixWord : Bool) : Word (encoding width) length :=
  ⟨fun position => if prefixWord then prefixBit width (index width length fits position)
    else addressBit width (index width length fits position)⟩

private lemma word_distinct (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width) (prefixWord : Bool)
    (left right : Fin length)
    (same : ((word width length fits prefixWord).bit left).wire =
      ((word width length fits prefixWord).bit right).wire) : left = right := by
  have values := congrArg Fin.val same
  cases prefixWord <;>
    simp only [word, Bool.false_eq_true, if_false, if_true, prefixBit_wire,
      addressBit_wire, index] at values
  all_goals
    apply Fin.ext
    omega

/-- Full ordinary arithmetic placement preserves the complement of both original pool operands. -/
def operands (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    Addition.TTK.WordPlacement (encoding width) length where
  addend := word width length fits false
  target := word width length fits true
  addendDistinct := word_distinct width length fits false
  targetDistinct := word_distinct width length fits true
  separate := fun left right => address_prefix_ne width
    (index width length fits left) (index width length fits right)
  onto := encoding_surjective width

private lemma conjunction_separate (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width)
    (selected : Fin (Addition.TTK.encoding length).width) :
    (operands width length fits).subsystem.wires selected ≠ (conjunctionBit width).wire := by
  change (wordPairSubsystem _ _ _ _ _).wires selected ≠ _
  refine Fin.addCases (m := length) (n := length) (fun source => ?_) (fun target => ?_) selected
  · rw [wordPairSubsystem_left]
    exact address_conjunction_ne width _
  · rw [wordPairSubsystem_right]
    exact prefix_conjunction_ne width _

/-- The complete actual subtraction subsystem includes its original arbitrary borrow output. -/
def subsystem (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    WireSubsystem (Addition.TTK.overflowEncoding length) (encoding width) :=
  (operands width length fits).subsystem.withFlag (conjunctionBit width)
    (conjunction_separate width length fits)

/-- Including the existing conjunction preserves each exact ordered operand wire. -/
lemma subsystem_word (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (position : Fin (Addition.TTK.encoding length).width) :
    (subsystem width length fits).wires (Fin.castAdd 1 position) =
      (operands width length fits).subsystem.wires position :=
  (operands width length fits).subsystem.withFlag_source _ _ position

/-- The actual borrow output is precisely the original conjunction, not a new clean bit. -/
lemma subsystem_borrow (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    (subsystem width length fits).wires
      (Fin.natAdd (Addition.TTK.encoding length).width (0 : Fin 1)) =
        (conjunctionBit width).wire :=
  (operands width length fits).subsystem.withFlag_flag _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
