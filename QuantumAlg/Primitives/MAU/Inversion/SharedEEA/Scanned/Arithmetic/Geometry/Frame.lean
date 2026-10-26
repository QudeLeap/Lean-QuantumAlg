/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total

/-!
# Full-carry geometry arithmetic on the existing shared pool

Before the streaming stage, the existing conjunction bit is the high bit
of a wider temporary arithmetic target. Two existing prefix positions pad
the original metadata operand. Every position belongs to the original
frame; the actual native TTK body preserves the entire complement. Later
clean-pool preparation must discharge both padding-zero promises before
identifying the operand with the original metadata value.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The four original finite metadata words retain their actual source order. -/
inductive Field where
  | coefficient
  | quotient
  | divisor
  | shift

/-- One more bit than the scan address holds all three complete metadata summands. -/
abbrev fullWidth (width : Nat) : Nat := ScanMetadata.addressWidth width + 1

private def fieldOffset : Field → Nat
  | .coefficient => 0
  | .quotient => 1
  | .divisor => 2
  | .shift => 3

/-- The literal original metadata lens; no word is read by a circuit-generating callback. -/
def fieldBit (width : Nat) (field : Field) (index : Fin width.size) :
    EncodedBit (encoding width) :=
  sourceBit width (match field with
    | .coefficient => coefficientLengthBit width index
    | .quotient => quotientLengthBit width index
    | .divisor => divisorLengthBit width index
    | .shift => shiftBit width index)

private lemma fieldBit_wire (width : Nat) (field : Field) (index : Fin width.size) :
    (fieldBit width field index).wire.val =
      2 * (width + 3) + fieldOffset field * width.size + index.val := by
  cases field <;>
    simp [fieldBit, fieldOffset, sourceBit_wire, coefficientLengthBit_wire,
      quotientLengthBit_wire, divisorLengthBit_wire, shiftBit_wire]

private lemma field_original (width : Nat) (field : Field) (index : Fin width.size) :
    (fieldBit width field index).wire.val < (SharedEEA.encoding width).width := by
  rw [fieldBit_wire, SharedEEA.encoding_width]
  have within := index.isLt
  cases field <;> simp only [fieldOffset] <;> omega

/-- The existing conjunction is the high bit; every original address bit follows in order. -/
def target (width : Nat) : Word (encoding width) (fullWidth width) where
  bit index := if zero : index.val = 0 then conjunctionBit width
    else addressBit width ⟨index.val - 1, by
      have within := index.isLt
      dsimp only [fullWidth] at within
      omega⟩

/-- The first two original prefix positions are actual preserved padding, followed by metadata. -/
def source (width : Nat) (positive : 1 ≤ width) (field : Field) :
    Word (encoding width) (fullWidth width) where
  bit index := if padding : index.val < 2 then
      prefixBit width ⟨index.val, by
        have sizePositive := Nat.size_pos.mpr positive
        unfold ScanMetadata.addressWidth
        omega⟩
    else fieldBit width field ⟨index.val - 2, by
      have within := index.isLt
      dsimp only [fullWidth, ScanMetadata.addressWidth] at within
      omega⟩

private lemma target_distinct (width : Nat) (left right : Fin (fullWidth width))
    (different : left ≠ right) :
    ((target width).bit left).wire ≠ ((target width).bit right).wire := by
  unfold target
  dsimp only
  split_ifs with first second
  · exact False.elim (different (Fin.ext (first.trans second.symm)))
  · exact (address_conjunction_ne width _).symm
  · exact address_conjunction_ne width _
  · apply address_address_ne
    intro same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    dsimp only at values
    omega

private lemma source_distinct (width : Nat) (positive : 1 ≤ width) (field : Field)
    (left right : Fin (fullWidth width)) (different : left ≠ right) :
    ((source width positive field).bit left).wire ≠
      ((source width positive field).bit right).wire := by
  unfold source
  dsimp only
  split_ifs with first second
  · apply prefix_prefix_ne
    intro same
    exact different (Fin.ext (congrArg
      (fun value : Fin (ScanMetadata.addressWidth width) => value.val) same))
  · intro same
    have values := congrArg Fin.val same
    rw [prefixBit_wire, fieldBit_wire, SharedEEA.encoding_width] at values
    have within := right.isLt
    dsimp only [fullWidth, ScanMetadata.addressWidth] at within
    cases field <;> simp only [fieldOffset] at values <;> omega
  · intro same
    have values := congrArg Fin.val same
    rw [fieldBit_wire, prefixBit_wire, SharedEEA.encoding_width] at values
    have within := left.isLt
    dsimp only [fullWidth, ScanMetadata.addressWidth] at within
    cases field <;> simp only [fieldOffset] at values <;> omega
  · intro same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    simp only [fieldBit_wire] at values
    change 2 * (width + 3) + fieldOffset field * width.size + (left.val - 2) =
      2 * (width + 3) + fieldOffset field * width.size + (right.val - 2) at values
    omega

private lemma separate (width : Nat) (positive : 1 ≤ width) (field : Field)
    (left right : Fin (fullWidth width)) :
    ((source width positive field).bit left).wire ≠ ((target width).bit right).wire := by
  unfold source target
  dsimp only
  split_ifs with padding zero
  · exact prefix_conjunction_ne width _
  · exact (address_prefix_ne width _ _).symm
  · intro same
    have values := congrArg Fin.val same
    have original := field_original width field
      (⟨left.val - 2, by
        have within := left.isLt
        dsimp only [fullWidth, ScanMetadata.addressWidth] at within
        omega⟩ : Fin width.size)
    rw [conjunctionBit_wire] at values
    omega
  · intro same
    have values := congrArg Fin.val same
    have original := field_original width field
      (⟨left.val - 2, by
        have within := left.isLt
        dsimp only [fullWidth, ScanMetadata.addressWidth] at within
        omega⟩ : Fin width.size)
    rw [addressBit_wire] at values
    omega

/-- A complete native operand placement with both real padding positions and the full carry. -/
def placement (width : Nat) (positive : 1 ≤ width) (field : Field) :
    Addition.TTK.WordPlacement (encoding width) (fullWidth width) where
  addend := source width positive field
  target := target width
  addendDistinct := by
    intro left right same
    by_contra different
    exact source_distinct width positive field left right different same
  targetDistinct := by
    intro left right same
    by_contra different
    exact target_distinct width left right different same
  separate := separate width positive field
  onto := encoding_surjective width

/-- Actual full-carry addition without allocation or a discarded finite metadata bit. -/
def program (width : Nat) (positive : 1 ≤ width) (field : Field) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width positive field).program

/-- The complete native two-word action, retaining every physical complementary position. -/
def step (width : Nat) (positive : 1 ≤ width) (field : Field) : Data width → Data width :=
  (placement width positive field).step

/-- Arbitrary coherent labels and references retain the exact original native arithmetic. -/
lemma program_realizes (width : Nat) (positive : 1 ≤ width) (field : Field)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width positive field) environment
      (step width positive field) :=
  (placement width positive field).program_realizes environment

/-- Every position outside the actual arithmetic target remains unchanged on all labels. -/
lemma step_observed (width : Nat) (positive : 1 ≤ width) (field : Field)
    (state : Data width) (bit : EncodedBit (encoding width))
    (outside : ∀ index, ((target width).bit index).wire ≠ bit.wire) :
    bit.get (step width positive field state) = bit.get state :=
  (placement width positive field).step_get_of_target_ne state bit outside

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGeometry
