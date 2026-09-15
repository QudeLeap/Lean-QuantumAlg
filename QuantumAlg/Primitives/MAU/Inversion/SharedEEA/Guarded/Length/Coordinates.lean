/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Coordinates

/-!
# Actual quotient and low-shift guard sources for native length writes

The source refreshes the two lengths only at the joint quotient-zero and
shift-zero boundary [LYL+26, sec_EEA/sub_regshare.tex:309-313]. Their actual
retained bits are added directly to the length writer's source prefix.
The output remains a real length-field bit, and the sole arbitrary work
bit remains original Iter. Thus no existing dirty bit is reused as a
simultaneous extra gate control.

The prefix order is quotient, low shift, retained other length, followed
by the exact physical payload region. These coordinates describe the
original low-counter predicate. Terminal-aware interpretation of the two
reused padding clock bits remains a separate required instruction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthCoordinates

noncomputable section

open EncodedBit LengthCoordinates

/-- All original quotient bits followed by all original low-shift bits. -/
def guardBit (width : Nat) (index : Fin (2 * width.size)) : EncodedBit (encoding width) :=
  if first : index.val < width.size then quotientLengthBit width ⟨index.val, first⟩
  else shiftBit width ⟨index.val - width.size, by have within := index.isLt; omega⟩

/-- Literal original physical addresses of both actual retained guard fields. -/
theorem guardBit_wire (width : Nat) (index : Fin (2 * width.size)) :
    (guardBit width index).wire.val =
      if index.val < width.size then 2 * (width + 3) + width.size + index.val
      else 2 * (width + 3) + 3 * width.size + (index.val - width.size) := by
  unfold guardBit
  split
  · rw [quotientLengthBit_wire]
  · rw [shiftBit_wire]

theorem guardBit_after_words (width : Nat) (index : Fin (2 * width.size)) :
    2 * (width + 3) ≤ (guardBit width index).wire.val := by
  rw [guardBit_wire]
  split <;> omega

theorem guardBit_before_flags (width : Nat) (index : Fin (2 * width.size)) :
    (guardBit width index).wire.val < 2 * (width + 3) + 4 * width.size := by
  have within := index.isLt
  rw [guardBit_wire]
  split <;> omega

/-- The two real guard fields contain no repeated source coordinate. -/
theorem guardBit_injective (width : Nat) :
    Function.Injective (fun index => (guardBit width index).wire) := by
  intro left right same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [guardBit_wire, guardBit_wire] at values
  have leftBound := left.isLt
  have rightBound := right.isLt
  apply Fin.ext
  split_ifs at values <;> omega

private theorem guard_boundary_ne (width : Nat) (field : Field) (guard : Fin (2 * width.size))
    (boundary : Fin width.size) :
    (guardBit width guard).wire ≠ (boundaryBit width field boundary).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [guardBit_wire, boundaryBit_wire] at values
  have guardBound := guard.isLt
  have boundaryBound := boundary.isLt
  cases field <;> simp only [reduceCtorEq, if_true, if_false] at values <;>
    split_ifs at values <;> omega

private theorem guard_payload_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (guard : Fin (2 * width.size)) (payload : Fin (region width field key)) :
    (guardBit width guard).wire ≠ (payloadBit width field key firstWord payload).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  have afterWords := guardBit_after_words width guard
  have beforeLengths := payloadBit_before_lengths width field key firstWord payload
  omega

/-- Guard sources are disjoint from the complete retained-boundary and payload source list. -/
theorem guard_source_ne (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (guard : Fin (2 * width.size)) (source : Fin (width.size + region width field key)) :
    (guardBit width guard).wire ≠
      (LengthCoordinates.sourceBit width field key firstWord source).wire := by
  unfold LengthCoordinates.sourceBit
  split
  · exact guard_boundary_ne width field guard _
  · exact guard_payload_ne width field key firstWord guard _

/-- A real guard bit is never the real length output, irrespective of the selected refresh. -/
theorem guard_output_ne (width : Nat) (field : Field) (guard : Fin (2 * width.size))
    (output : Fin width.size) :
    (guardBit width guard).wire ≠ (outputBit width field output).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [guardBit_wire] at values
  have guardBound := guard.isLt
  have outputBound := output.rev.isLt
  cases field <;> simp only [outputBit, coefficientLengthBit_wire,
    divisorLengthBit_wire] at values <;> split_ifs at values <;> omega

/-- Guard values are physical length bits, so they never overlap the original Iter work bit. -/
theorem guard_work_ne (width : Nat) (guard : Fin (2 * width.size)) :
    (guardBit width guard).wire ≠ (iterationBit width).wire := by
  intro same
  have values := congrArg (fun index : Fin (encoding width).width => index.val) same
  rw [iterationBit_wire] at values
  have beforeFlags := guardBit_before_flags width guard
  omega

/-- The prefix contains exactly the three retained original finite length fields. -/
def prefixWidth (width : Nat) : Nat := 3 * width.size

/-- Append the original writer's sources after both real retained guard fields. -/
def sourceBit (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (prefixWidth width + region width field key)) : EncodedBit (encoding width) :=
  if leading : index.val < 2 * width.size then guardBit width ⟨index.val, leading⟩
  else LengthCoordinates.sourceBit width field key firstWord
    ⟨index.val - 2 * width.size, by
      have within := index.isLt
      unfold prefixWidth at within
      omega⟩

/-- Every actual source is unique across both guards and the complete original writer. -/
theorem sourceBit_injective (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) :
    Function.Injective (fun index => (sourceBit width field key firstWord index).wire) := by
  intro left right same
  unfold sourceBit at same
  dsimp only at same
  split at same
  · split at same
    · have positions := guardBit_injective width same
      exact Fin.ext (congrArg (fun index : Fin (2 * width.size) => index.val) positions)
    · exact False.elim (guard_source_ne width field key firstWord _ _ same)
  · split at same
    · exact False.elim (guard_source_ne width field key firstWord _ _ same.symm)
    · have positions := LengthCoordinates.sourceBit_injective width field key firstWord same
      have values := congrArg
        (fun index : Fin (width.size + region width field key) => index.val) positions
      change left.val - 2 * width.size = right.val - 2 * width.size at values
      apply Fin.ext
      omega

/-- The actual output lies outside the enlarged actual source prefix and physical payload. -/
theorem source_output_ne (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (output : Fin width.size)
    (index : Fin (prefixWidth width + region width field key)) :
    (sourceBit width field key firstWord index).wire ≠ (outputBit width field output).wire := by
  unfold sourceBit
  split
  · exact guard_output_ne width field _ output
  · exact LengthCoordinates.source_output_ne width field key firstWord output _

/-- The enlarged actual source list still borrows only the original arbitrary Iter bit. -/
theorem source_work_ne (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (prefixWidth width + region width field key)) :
    (sourceBit width field key firstWord index).wire ≠ (iterationBit width).wire := by
  unfold sourceBit
  split
  · exact guard_work_ne width _
  · exact LengthCoordinates.source_work_ne width field key firstWord _

/-- The actual guarded writer layout uses no wire outside the existing complete frame. -/
def layout (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (output : Fin width.size) :
    Word.OneDirtyLayout (encoding := encoding width)
      (prefixWidth width + region width field key) where
  source := ⟨sourceBit width field key firstWord⟩
  output := outputBit width field output
  work := iterationBit width
  source_injective := sourceBit_injective width field key firstWord
  source_output_ne := source_output_ne width field key firstWord output
  source_work_ne := source_work_ne width field key firstWord
  work_output_ne := LengthCoordinates.work_output_ne width field output

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthCoordinates
