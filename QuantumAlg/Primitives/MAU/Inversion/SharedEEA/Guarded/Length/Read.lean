/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Length.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Length.Read

/-!
# Exact retained-field reads of the native length-refresh boundary guard

The added source prefix reads all actual quotient and low-shift bits,
followed by the actual other length field. Matching its fixed pattern is
exactly the original source boundary and that retained key
[LYL+26, sec_EEA/sub_regshare.tex:309-313]. Output length flips preserve
both guard registers. Terminal padding-clock dispatch remains separate
from this literal original low-counter condition.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthRead

noncomputable section

open EncodedBit LengthCoordinates GuardedLengthCoordinates

/-- The literal original retained-field condition at the length-refresh boundary. -/
def Guard {width : Nat} (state : Registers width) : Prop :=
  state.quotientLength = 0#width.size ∧ state.shift = 0#width.size

private instance guardDecidable {width : Nat} (state : Registers width) :
    Decidable (Guard state) := by
  unfold Guard
  infer_instance

/-- Each added guard source reads the corresponding original finite field bit. -/
theorem guardBit_get (width : Nat) (index : Fin (2 * width.size)) (state : Registers width) :
    (guardBit width index).get state =
      if index.val < width.size then state.quotientLength.getMsbD index.val
      else state.shift.getMsbD (index.val - width.size) := by
  unfold guardBit
  split
  · exact quotientLengthBit_get width _ state
  · exact shiftBit_get width _ state

/-- Testing all actual guard sources for zero is precisely the complete two-field boundary test. -/
theorem guard_matches_iff (width : Nat) (state : Registers width) :
    (∀ index : Fin (2 * width.size), (guardBit width index).get state = false) ↔ Guard state := by
  constructor
  · intro matched
    constructor
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      have actual := matched ⟨index, by omega⟩
      rw [guardBit_get, if_pos within] at actual
      exact actual.trans (BitVec.getMsbD_zero (w := width.size) (i := index)).symm
    · apply BitVec.eq_of_getMsbD_eq
      intro index within
      have actual := matched ⟨width.size + index, by omega⟩
      have afterQuotient : ¬width.size + index < width.size := by omega
      rw [guardBit_get, if_neg afterQuotient, Nat.add_sub_cancel_left] at actual
      exact actual.trans (BitVec.getMsbD_zero (w := width.size) (i := index)).symm
  · rintro ⟨quotientZero, shiftZero⟩ index
    rw [guardBit_get]
    split
    · rw [quotientZero, BitVec.getMsbD_zero]
    · rw [shiftZero, BitVec.getMsbD_zero]

/-- Embed a guard bit at its unchanged prefix position. -/
def guardIndex (width : Nat) (index : Fin (2 * width.size)) : Fin (prefixWidth width) :=
  ⟨index.val, by unfold prefixWidth; have within := index.isLt; omega⟩

/-- Embed a retained-key bit after both actual guard fields. -/
def boundaryIndex (width : Nat) (index : Fin width.size) : Fin (prefixWidth width) :=
  ⟨2 * width.size + index.val, by unfold prefixWidth; have within := index.isLt; omega⟩

/-- The actual source prefix, before the physical payload begins. -/
def prefixBit (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (prefixWidth width)) : EncodedBit (encoding width) :=
  GuardedLengthCoordinates.sourceBit width field key firstWord
    ⟨index.val, by have within := index.isLt; omega⟩

/-- A guard embedding selects precisely the original quotient or low-shift physical lens. -/
theorem prefixBit_guard (width : Nat) (field : Field) (key : BitVec width.size) (firstWord : Bool)
    (index : Fin (2 * width.size)) :
    prefixBit width field key firstWord (guardIndex width index) = guardBit width index := by
  change GuardedLengthCoordinates.sourceBit width field key firstWord ⟨index.val, _⟩ = _
  rw [GuardedLengthCoordinates.sourceBit, dif_pos index.isLt]

/-- A boundary embedding selects precisely the original other length-field lens. -/
theorem prefixBit_boundary (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (index : Fin width.size) :
    prefixBit width field key firstWord (boundaryIndex width index) =
      boundaryBit width field index := by
  have afterGuard : ¬2 * width.size + index.val < 2 * width.size := by omega
  change GuardedLengthCoordinates.sourceBit width field key firstWord
    ⟨2 * width.size + index.val, _⟩ = _
  rw [GuardedLengthCoordinates.sourceBit, dif_neg afterGuard]
  have original :
      (⟨2 * width.size + index.val - 2 * width.size, by
        have within := index.isLt
        omega⟩ : Fin (width.size + region width field key)) =
          ⟨index.val, by have within := index.isLt; omega⟩ := by
    apply Fin.ext
    change 2 * width.size + index.val - 2 * width.size = index.val
    omega
  rw [original, LengthCoordinates.sourceBit, dif_pos index.isLt]

/-- The fixed source pattern has zero guard bits and exactly the selected finite boundary key. -/
def expected (width : Nat) (key : BitVec width.size) (index : Fin (prefixWidth width)) : Bool :=
  if index.val < 2 * width.size then false else key.getMsbD (index.val - 2 * width.size)

theorem expected_guard (width : Nat) (key : BitVec width.size) (index : Fin (2 * width.size)) :
    expected width key (guardIndex width index) = false := by
  exact if_pos index.isLt

theorem expected_boundary (width : Nat) (key : BitVec width.size) (index : Fin width.size) :
    expected width key (boundaryIndex width index) = key.getMsbD index.val := by
  have afterGuard : ¬2 * width.size + index.val < 2 * width.size := by omega
  change (if 2 * width.size + index.val < 2 * width.size then false
    else key.getMsbD (2 * width.size + index.val - 2 * width.size)) = _
  rw [if_neg afterGuard]
  exact congrArg key.getMsbD (Nat.add_sub_cancel_left _ _)

/-- The actual full prefix matches exactly the real boundary guard and retained key. -/
theorem prefix_matches_iff (width : Nat) (field : Field) (key : BitVec width.size)
    (firstWord : Bool) (state : Registers width) :
    (∀ index : Fin (prefixWidth width),
      (prefixBit width field key firstWord index).get state = expected width key index) ↔
        Guard state ∧ boundaryValue field state = key := by
  constructor
  · intro matched
    constructor
    · apply (guard_matches_iff width state).mp
      intro index
      have actual := matched (guardIndex width index)
      rw [prefixBit_guard, expected_guard] at actual
      exact actual
    · apply (LengthRead.boundary_matches_iff width field key state).mp
      intro index
      have actual := matched (boundaryIndex width index)
      rw [prefixBit_boundary, expected_boundary] at actual
      exact actual
  · rintro ⟨guarded, boundary⟩ index
    by_cases leading : index.val < 2 * width.size
    · let original : Fin (2 * width.size) := ⟨index.val, leading⟩
      have same : guardIndex width original = index := Fin.ext rfl
      rw [← same, prefixBit_guard, expected_guard]
      exact (guard_matches_iff width state).mpr guarded original
    · have within : index.val - 2 * width.size < width.size := by
        have bound := index.isLt
        unfold prefixWidth at bound
        omega
      let original : Fin width.size := ⟨index.val - 2 * width.size, within⟩
      have same : boundaryIndex width original = index := by
        apply Fin.ext
        change 2 * width.size + (index.val - 2 * width.size) = index.val
        omega
      rw [← same, prefixBit_boundary, expected_boundary]
      exact (LengthRead.boundary_matches_iff width field key state).mpr boundary original

/-- Every actual target length flip preserves the complete original boundary guard. -/
theorem guard_output_flip (width : Nat) (field : Field) (output : Fin width.size)
    (state : Registers width) :
    Guard ((outputBit width field output).flip state) ↔ Guard state := by
  cases field <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.GuardedLengthRead
