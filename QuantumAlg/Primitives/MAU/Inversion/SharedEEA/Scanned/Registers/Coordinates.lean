/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers

/-!
# Actual nonoverlapping source and scan-pool coordinates

Each address, prefix and conjunction wire has an explicit position after the
unchanged original register frame. The certificates below concern complete
physical supports, independently of data values or EEA trajectory promises.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Every original wire stays at its original source-frame position. -/
lemma sourceBit_wire (width : Nat) (bit : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width bit).wire.val = bit.wire.val := by rfl

/-- Lifting preserves distinct physical source positions. -/
lemma source_source_ne (width : Nat) (left right : EncodedBit (SharedEEA.encoding width))
    (different : left.wire ≠ right.wire) :
    (sourceBit width left).wire ≠ (sourceBit width right).wire := by
  intro same
  apply different
  apply Fin.ext
  have values := congrArg (fun wire : Fin (encoding width).width => wire.val) same
  exact values

/-- The address starts immediately after every original source wire. -/
lemma addressBit_wire (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (addressBit width index).wire.val = (SharedEEA.encoding width).width + index.val := by rfl

/-- Prefix storage follows the complete address, including its carry position. -/
lemma prefixBit_wire (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (prefixBit width index).wire.val = (SharedEEA.encoding width).width +
      ScanMetadata.addressWidth width + index.val := by
  change (SharedEEA.encoding width).width + (ScanMetadata.addressWidth width + index.val) = _
  omega

/-- The conjunction is the final new wire, after both complete pool words. -/
lemma conjunctionBit_wire (width : Nat) :
    (conjunctionBit width).wire.val = (SharedEEA.encoding width).width +
      2 * ScanMetadata.addressWidth width := by
  change (SharedEEA.encoding width).width +
    (ScanMetadata.addressWidth width + (ScanMetadata.addressWidth width + 0)) = _
  omega

/-- An actual source wire cannot be borrowed as an address wire. -/
lemma source_address_ne (width : Nat) (bit : EncodedBit (SharedEEA.encoding width))
    (index : Fin (ScanMetadata.addressWidth width)) :
    (sourceBit width bit).wire ≠ (addressBit width index).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [sourceBit_wire, addressBit_wire] at value
  have within := bit.wire.isLt
  omega

/-- The prefix workspace also lies outside the complete source frame. -/
lemma source_prefix_ne (width : Nat) (bit : EncodedBit (SharedEEA.encoding width))
    (index : Fin (ScanMetadata.addressWidth width)) :
    (sourceBit width bit).wire ≠ (prefixBit width index).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [sourceBit_wire, prefixBit_wire] at value
  have within := bit.wire.isLt
  omega

/-- The conjunction wire is distinct from every preserved source bit. -/
lemma source_conjunction_ne (width : Nat) (bit : EncodedBit (SharedEEA.encoding width)) :
    (sourceBit width bit).wire ≠ (conjunctionBit width).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [sourceBit_wire, conjunctionBit_wire] at value
  have within := bit.wire.isLt
  omega

/-- Every address position is distinct from every unary-prefix position. -/
lemma address_prefix_ne (width : Nat) (first second : Fin (ScanMetadata.addressWidth width)) :
    (addressBit width first).wire ≠ (prefixBit width second).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [addressBit_wire, prefixBit_wire] at value
  have within := first.isLt
  omega

/-- The complete address word excludes the conjunction wire. -/
lemma address_conjunction_ne (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (addressBit width index).wire ≠ (conjunctionBit width).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [addressBit_wire, conjunctionBit_wire] at value
  have within := index.isLt
  omega

/-- Prefix work excludes the separate conjunction wire. -/
lemma prefix_conjunction_ne (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (prefixBit width index).wire ≠ (conjunctionBit width).wire := by
  intro same
  have value := congrArg Fin.val same
  rw [prefixBit_wire, conjunctionBit_wire] at value
  have within := index.isLt
  omega

/-- Distinct address positions are genuinely distinct physical wires. -/
lemma address_address_ne (width : Nat) (first second : Fin (ScanMetadata.addressWidth width))
    (different : first ≠ second) :
    (addressBit width first).wire ≠ (addressBit width second).wire := by
  intro same
  apply different
  apply Fin.ext
  have value := congrArg Fin.val same
  rw [addressBit_wire, addressBit_wire] at value
  omega

/-- Distinct prefix positions are genuinely distinct physical wires. -/
lemma prefix_prefix_ne (width : Nat) (first second : Fin (ScanMetadata.addressWidth width))
    (different : first ≠ second) :
    (prefixBit width first).wire ≠ (prefixBit width second).wire := by
  intro same
  apply different
  apply Fin.ext
  have value := congrArg Fin.val same
  rw [prefixBit_wire, prefixBit_wire] at value
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned
