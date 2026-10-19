/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout

/-!
# Actual native source and target coordinates for both length refreshes

The coefficient refresh reads the left little-endian region ending before
the old divisor boundary. The divisor refresh reads the right big-endian
region selected by the already refreshed coefficient length
[LYL+26, sec_EEA/sub_regshare.tex:309-313]. Each static finite boundary key
therefore selects a literal subset of original work-word positions.

The actual source consists of the other retained length field and that
word region in most-significant-first order. The target is an actual bit
of the length being updated, and arbitrary original Iter is the only work
bit. All physical disjointness is proved on the full original encoding.
Natural subtraction makes an oversized boundary key select an empty region;
no region-validity or clean-work condition is imposed on a caller.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LengthCoordinates

noncomputable section

open EncodedBit

/-- The source's two length writes, each controlled by the other retained length boundary. -/
inductive Field where
  | coefficient
  | divisor
deriving DecidableEq

/-- The boundary is an actual complete finite register, including leading zeros. -/
def boundaryValue {width : Nat} : Field → Registers width → BitVec width.size
  | .coefficient, state => state.divisorLength
  | .divisor, state => state.coefficientLength

/-- Literal source region width at a fixed finite key; every natural subtraction is retained. -/
def region (width : Nat) (field : Field) (key : BitVec width.size) : Nat :=
  match field with
  | .coefficient => width + 3 - key.toNat
  | .divisor => width + 3 - 1 - key.toNat

/-- Every static region lies inside its actual original full work word. -/
lemma region_le (width : Nat) (field : Field) (key : BitVec width.size) :
    region width field key ≤ width + 3 := by
  cases field <;> simp only [region] <;> omega

/-- Exact physical word position when the selected region is read most-significant-first. -/
def payloadPosition (width : Nat) (field : Field) (key : BitVec width.size)
    (index : Fin (region width field key)) : Fin (width + 3) :=
  match field with
  | .coefficient => ⟨region width .coefficient key - 1 - index.val, by
      have within := index.isLt
      have bounded := region_le width .coefficient key
      omega⟩
  | .divisor => ⟨width + 3 - region width .divisor key + index.val, by
      have within := index.isLt
      have bounded := region_le width .divisor key
      omega⟩

/-- Reading a selected region never duplicates a physical word coordinate. -/
lemma payloadPosition_injective (width : Nat) (field : Field) (key : BitVec width.size) :
    Function.Injective (payloadPosition width field key) := by
  intro left right same
  have values := congrArg (fun index : Fin (width + 3) => index.val) same
  have leftBound := left.isLt
  have rightBound := right.isLt
  apply Fin.ext
  cases field <;> simp only [payloadPosition] at values <;> omega

/-- The actual original Work1 or Work2 bit at that explicit region coordinate. -/
def payloadBit (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (region width field key)) : EncodedBit (encoding width) :=
  if firstWord then firstWordBit width (payloadPosition width field key index)
  else secondWordBit width (payloadPosition width field key index)

/-- Literal original work-word physical address for either actual word. -/
lemma payloadBit_wire (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (region width field key)) :
    (payloadBit width field key firstWord index).wire.val =
      (if firstWord then 0 else width + 3) + (payloadPosition width field key index).val := by
  cases firstWord <;> simp only [payloadBit, Bool.false_eq_true, if_false, if_true,
    firstWordBit_wire, secondWordBit_wire, Nat.zero_add]

/-- All payload sources belong to the original two work words. -/
lemma payloadBit_before_lengths (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin (region width field key)) :
    (payloadBit width field key firstWord index).wire.val < 2 * (width + 3) := by
  rw [payloadBit_wire]
  have within := (payloadPosition width field key index).isLt
  cases firstWord <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- Each selected original word is read without repeating a wire. -/
lemma payloadBit_injective (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) :
    Function.Injective (fun index => (payloadBit width field key firstWord index).wire) := by
  intro left right same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [payloadBit_wire, payloadBit_wire] at values
  apply payloadPosition_injective width field key
  apply Fin.ext
  omega

/-- Boundary-key bits use the actual other length field in most-significant-first order. -/
def boundaryBit (width : Nat) : Field → Fin width.size → EncodedBit (encoding width)
  | .coefficient, index => divisorLengthBit width index
  | .divisor, index => coefficientLengthBit width index

/-- Constant length writes address the target field in least-significant-first order. -/
def outputBit (width : Nat) : Field → Fin width.size → EncodedBit (encoding width)
  | .coefficient, index => coefficientLengthBit width index.rev
  | .divisor, index => divisorLengthBit width index.rev

/-- Actual boundary-key bit values are those of the original complete finite boundary word. -/
lemma boundaryBit_get (width : Nat) (field : Field) (index : Fin width.size)
    (state : Registers width) :
    (boundaryBit width field index).get state = (boundaryValue field state).getMsbD index.val := by
  cases field with
  | coefficient => exact divisorLengthBit_get width index state
  | divisor => exact coefficientLengthBit_get width index state

/-- The source boundary field's physical offset in the full original register encoding. -/
lemma boundaryBit_wire (width : Nat) (field : Field) (index : Fin width.size) :
    (boundaryBit width field index).wire.val =
      2 * (width + 3) + (if field = .coefficient then 2 * width.size else 0) + index.val := by
  cases field <;> simp only [boundaryBit, divisorLengthBit_wire, coefficientLengthBit_wire,
    reduceCtorEq, if_true, if_false, Nat.add_zero]

/-- The actual output field is disjoint from its boundary-key field. -/
lemma boundary_output_ne (width : Nat) (field : Field) (input output : Fin width.size) :
    (boundaryBit width field input).wire ≠ (outputBit width field output).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  have inputBound := input.isLt
  have outputBound := output.rev.isLt
  cases field <;> simp only [boundaryBit, outputBit, divisorLengthBit_wire,
    coefficientLengthBit_wire] at values <;> omega

/-- Distinct boundary-key positions read distinct original physical wires. -/
lemma boundaryBit_injective (width : Nat) (field : Field) :
    Function.Injective (fun index => (boundaryBit width field index).wire) := by
  intro left right same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [boundaryBit_wire, boundaryBit_wire] at values
  apply Fin.ext
  omega

/-- Concatenate the complete actual boundary key with the selected original word region. -/
def sourceBit (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (width.size + region width field key)) : EncodedBit (encoding width) :=
  if leading : index.val < width.size then boundaryBit width field ⟨index.val, leading⟩
  else payloadBit width field key firstWord ⟨index.val - width.size,
    by have within := index.isLt; omega⟩

private lemma boundary_payload_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (boundary : Fin width.size) (payload : Fin (region width field key)) :
    (boundaryBit width field boundary).wire ≠
      (payloadBit width field key firstWord payload).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [boundaryBit_wire] at values
  have within := payloadBit_before_lengths width field key firstWord payload
  omega

private lemma payload_output_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (payload : Fin (region width field key)) (output : Fin width.size) :
    (payloadBit width field key firstWord payload).wire ≠ (outputBit width field output).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  have within := payloadBit_before_lengths width field key firstWord payload
  cases field <;> simp only [outputBit, coefficientLengthBit_wire,
    divisorLengthBit_wire] at values <;> omega

/-- Every actual source coordinate is unique across the retained key and original word region. -/
lemma sourceBit_injective (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) :
    Function.Injective (fun index => (sourceBit width field key firstWord index).wire) := by
  intro left right same
  unfold sourceBit at same
  dsimp only at same
  split at same
  · split at same
    · have positions := boundaryBit_injective width field same
      exact Fin.ext (congrArg (fun index : Fin width.size => index.val) positions)
    · exact False.elim (boundary_payload_ne width field key firstWord _ _ same)
  · split at same
    · exact False.elim (boundary_payload_ne width field key firstWord _ _ same.symm)
    · have positions := payloadBit_injective width field key firstWord same
      have values := congrArg (fun index : Fin (region width field key) => index.val) positions
      change left.val - width.size = right.val - width.size at values
      apply Fin.ext
      omega

/-- The chosen actual output wire lies outside every source coordinate. -/
lemma source_output_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size)
    (index : Fin (width.size + region width field key)) :
    (sourceBit width field key firstWord index).wire ≠ (outputBit width field output).wire := by
  unfold sourceBit
  split
  · exact boundary_output_ne width field _ output
  · exact payload_output_ne width field key firstWord _ output

/-- Original Iter is disjoint from all original boundary and payload sources. -/
lemma source_work_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin (width.size + region width field key)) :
    (sourceBit width field key firstWord index).wire ≠ (iterationBit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [iterationBit_wire] at values
  unfold sourceBit at values
  split at values
  · rw [boundaryBit_wire] at values
    have within := index.isLt
    split_ifs at values <;> omega
  · have within := payloadBit_before_lengths width field key firstWord
      ⟨index.val - width.size, by have bounded := index.isLt; omega⟩
    omega

/-- Original Iter is also disjoint from the actual length output. -/
lemma work_output_ne (width : Nat) (field : Field) (output : Fin width.size) :
    (iterationBit width).wire ≠ (outputBit width field output).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  have within := output.rev.isLt
  cases field <;> simp only [outputBit, coefficientLengthBit_wire, divisorLengthBit_wire,
    iterationBit_wire] at values <;> omega

/-- Exact one-dirty native layout for a boundary key, a word region, and one real length output. -/
def layout (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (output : Fin width.size) :
    Word.OneDirtyLayout (encoding := encoding width) (width.size + region width field key) where
  source := ⟨sourceBit width field key firstWord⟩
  output := outputBit width field output
  work := iterationBit width
  source_injective := sourceBit_injective width field key firstWord
  source_output_ne := source_output_ne width field key firstWord output
  source_work_ne := source_work_ne width field key firstWord
  work_output_ne := work_output_ne width field output

end

end QuantumAlg.MAU.Inversion.SharedEEA.LengthCoordinates
