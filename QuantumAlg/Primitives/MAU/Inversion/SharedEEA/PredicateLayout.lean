/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest
import Mathlib.Data.Nat.Basic

/-!
# Physical layouts for the shared-EEA length predicates

The phase and exchange conditions read the actual quotient, divisor, and
shift lengths, and write the separately allocated Ctrl bit
[LYL+26, sec_EEA/sub_regshare.tex:22-26,303-315]. Each layout here borrows
only a prefix of the existing Work2 word for the conjunction chain. The
static capacity proof covers every width and does not require those bits
to be zero. Work1, including the two reused terminal counter bits, is not
used as conjunction work.

`ZeroTestLayout` supplies wire separation to both the original clean-work
construction and the arbitrary-work construction. Defining this layout
does not assert cleanliness or execute the clean-work construction. The
arbitrary-work gate correctness and exact restoration must be applied at
the eventual call site. No additional storage is allocated here.

The extended-clock layout reads the actual Work1 high bits and the low
shift register together. Selecting this repaired zero predicate at the
proper terminal boundary remains separate from the source's active
low-counter predicate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PredicateLayout

noncomputable section

open EncodedBit

/-- The three actual source lengths used by the post-arithmetic predicates. -/
inductive LengthField where
  | quotient
  | divisor
  | shift
deriving DecidableEq

private def lengthOffset : LengthField → Nat
  | .quotient => 1
  | .divisor => 2
  | .shift => 3

/-- Select the actual retained finite length value; this is not a second store. -/
def lengthValue {width : Nat} (field : LengthField) (state : Registers width) :
    BitVec width.size :=
  match field with
  | .quotient => state.quotientLength
  | .divisor => state.divisorLength
  | .shift => state.shift

/-- Select a bit of that same encoded length register. -/
def lengthBit (width : Nat) (field : LengthField) (index : Fin width.size) :
    EncodedBit (encoding width) :=
  match field with
  | .quotient => quotientLengthBit width index
  | .divisor => divisorLengthBit width index
  | .shift => shiftBit width index

theorem lengthBit_get (width : Nat) (field : LengthField) (index : Fin width.size)
    (state : Registers width) :
    (lengthBit width field index).get state = (lengthValue field state).getMsbD index.val := by
  cases field
  · exact quotientLengthBit_get width index state
  · exact divisorLengthBit_get width index state
  · exact shiftBit_get width index state

private theorem lengthBit_wire (width : Nat) (field : LengthField) (index : Fin width.size) :
    (lengthBit width field index).wire.val =
      2 * (width + 3) + lengthOffset field * width.size + index.val := by
  cases field
  · simpa only [lengthBit, lengthOffset, Nat.one_mul] using quotientLengthBit_wire width index
  · exact divisorLengthBit_wire width index
  · exact shiftBit_wire width index

private theorem lengthBit_after_words (width : Nat) (field : LengthField)
    (index : Fin width.size) :
    2 * (width + 3) ≤ (lengthBit width field index).wire.val := by
  rw [lengthBit_wire]
  omega

private theorem lengthBit_before_control (width : Nat) (field : LengthField)
    (index : Fin width.size) :
    (lengthBit width field index).wire.val < (controlBit width).wire.val := by
  rw [lengthBit_wire, controlBit_wire]
  have within := index.isLt
  cases field <;> simp only [lengthOffset] <;> omega

private theorem lengthBit_injective (width : Nat) (field : LengthField) :
    Function.Injective (fun index : Fin width.size => (lengthBit width field index).wire) := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  rw [lengthBit_wire, lengthBit_wire] at values
  omega

private theorem lengthBit_distinct (width : Nat) (first second : LengthField)
    (different : first ≠ second) (left right : Fin width.size) :
    (lengthBit width first left).wire ≠ (lengthBit width second right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [lengthBit_wire, lengthBit_wire] at values
  have leftBound := left.isLt
  have rightBound := right.isLt
  cases first <;> cases second
  all_goals try exact different rfl
  all_goals simp only [lengthOffset] at values
  all_goals omega

/-- Even two length registers need at most `n` arbitrary conjunction-work bits. -/
theorem pair_work_capacity (width : Nat) : 2 * width.size - 2 ≤ width := by
  by_cases empty : width.size = 0
  · simp only [empty, Nat.mul_zero, Nat.zero_sub, Nat.zero_le]
  · have previous : width.size - 1 < width.size := by omega
    have powerBound := Nat.lt_size.mp previous
    have linearBound := Nat.mul_le_pow (by decide : 2 ≠ 1) (width.size - 1)
    omega

private theorem size_capacity (width : Nat) : width.size ≤ width :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Every nontrivial modulus supplies the static at-least-two length width. -/
theorem modulus_length_width (modulus : Nat) (nontrivial : 1 < modulus) :
    2 ≤ modulus.size.size := by
  have modulusWidth : 1 < modulus.size := Nat.lt_size.mpr nontrivial
  have lengthWidth : 1 < modulus.size.size := Nat.lt_size.mpr modulusWidth
  omega

/-- A dirty work lens uses an existing Work2 bit, with no value assumption. -/
def workBit (width count : Nat) (capacity : count ≤ width + 3) (index : Fin count) :
    EncodedBit (encoding width) :=
  secondWordBit width ⟨index.val, lt_of_lt_of_le index.isLt capacity⟩

theorem workBit_get (width count : Nat) (capacity : count ≤ width + 3) (index : Fin count)
    (state : Registers width) :
    (workBit width count capacity index).get state = state.secondWord.getMsbD index.val :=
  secondWordBit_get width _ state

theorem workBit_wire (width count : Nat) (capacity : count ≤ width + 3) (index : Fin count) :
    (workBit width count capacity index).wire.val = width + 3 + index.val :=
  secondWordBit_wire width _

private def fromSource (width count : Nat) (capacity : count ≤ width + 3)
    (source : Word (encoding width) (count + 2))
    (distinct : Function.Injective (fun index => (source.bit index).wire))
    (outside : ∀ index, (source.bit index).wire.val < width + 3 ∨
      2 * (width + 3) ≤ (source.bit index).wire.val)
    (beforeControl : ∀ index, (source.bit index).wire.val < (controlBit width).wire.val) :
    Word.ZeroTestLayout (encoding := encoding width) count where
  source := source
  output := controlBit width
  work := ⟨workBit width count capacity⟩
  source_source_ne := fun _ _ different same => different (distinct same)
  source_output_ne := by
    intro index same
    exact (Nat.ne_of_lt (beforeControl index)) (congrArg Fin.val same)
  source_work_ne := by
    intro sourceIndex workIndex same
    have values := congrArg Fin.val same
    change (source.bit sourceIndex).wire.val = (workBit width count capacity workIndex).wire.val
      at values
    rw [workBit_wire] at values
    have separation := outside sourceIndex
    have bound := workIndex.isLt
    omega
  work_work_ne := by
    intro left right different same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    change (workBit width count capacity left).wire.val =
      (workBit width count capacity right).wire.val at values
    rw [workBit_wire, workBit_wire] at values
    omega
  work_output_ne := by
    intro index same
    have values := congrArg Fin.val same
    change (workBit width count capacity index).wire.val = (controlBit width).wire.val at values
    rw [workBit_wire, controlBit_wire] at values
    have bound := index.isLt
    omega

/-- Wire layout for one actual length, using only its required Work2 prefix as dirty work. -/
def single (width : Nat) (field : LengthField) (enough : 2 ≤ width.size) :
    Word.ZeroTestLayout (encoding := encoding width) (width.size - 2) :=
  fromSource width (width.size - 2) (by have bound := size_capacity width; omega)
    ⟨fun index => lengthBit width field ⟨index.val, by have bound := index.isLt; omega⟩⟩
    (by
      intro left right same
      have selected := lengthBit_injective width field same
      exact Fin.ext (congrArg (fun index : Fin width.size => index.val) selected))
    (fun index => Or.inr (lengthBit_after_words width field _))
    (fun index => lengthBit_before_control width field _)

theorem single_source_get (width : Nat) (field : LengthField) (enough : 2 ≤ width.size)
    (index : Fin (width.size - 2 + 2)) (state : Registers width) :
    ((single width field enough).source.bit index).get state =
      (lengthValue field state).getMsbD index.val :=
  lengthBit_get width field _ state

private def pairBit (width : Nat) (first second : LengthField) (index : Fin (2 * width.size)) :
    EncodedBit (encoding width) :=
  if initial : index.val < width.size then lengthBit width first ⟨index.val, initial⟩
  else lengthBit width second ⟨index.val - width.size, by have bound := index.isLt; omega⟩

private theorem pairBit_injective (width : Nat) (first second : LengthField)
    (different : first ≠ second) :
    Function.Injective
      (fun index : Fin (2 * width.size) => (pairBit width first second index).wire) := by
  intro left right same
  change (pairBit width first second left).wire = (pairBit width first second right).wire at same
  unfold pairBit at same
  split at same <;> split at same
  · have selected := lengthBit_injective width first same
    exact Fin.ext (congrArg (fun index : Fin width.size => index.val) selected)
  · exact False.elim (lengthBit_distinct width first second different _ _ same)
  · exact False.elim (lengthBit_distinct width first second different _ _ same.symm)
  · apply Fin.ext
    have selected := congrArg (fun index : Fin width.size => index.val)
      (lengthBit_injective width second same)
    dsimp only at selected
    omega

/-- Read two distinct actual lengths, retaining the original Ctrl as the xor-output wire. -/
def pair (width : Nat) (first second : LengthField) (different : first ≠ second)
    (enough : 2 ≤ width.size) :
    Word.ZeroTestLayout (encoding := encoding width) (2 * width.size - 2) :=
  fromSource width (2 * width.size - 2) (by have bound := pair_work_capacity width; omega)
    ⟨fun index => pairBit width first second ⟨index.val, by have bound := index.isLt; omega⟩⟩
    (by
      intro left right same
      have selected := pairBit_injective width first second different same
      exact Fin.ext (congrArg (fun index : Fin (2 * width.size) => index.val) selected))
    (by
      intro index
      apply Or.inr
      dsimp only
      unfold pairBit
      split <;> exact lengthBit_after_words width _ _)
    (by
      intro index
      dsimp only
      unfold pairBit
      split <;> exact lengthBit_before_control width _ _)

theorem pair_source_get (width : Nat) (first second : LengthField)
    (different : first ≠ second) (enough : 2 ≤ width.size)
    (index : Fin (2 * width.size - 2 + 2)) (state : Registers width) :
    ((pair width first second different enough).source.bit index).get state =
      if index.val < width.size then (lengthValue first state).getMsbD index.val
      else (lengthValue second state).getMsbD (index.val - width.size) := by
  change (pairBit width first second _).get state = _
  unfold pairBit
  split <;> exact lengthBit_get width _ _ state

/-- Quotient and divisor zero tests combine to give `quotient = 0` and `divisor ≠ 0`. -/
def quotientDivisor (width : Nat) (enough : 2 ≤ width.size) :
    Word.ZeroTestLayout (encoding := encoding width) (2 * width.size - 2) :=
  pair width .quotient .divisor (by decide) enough

/-- The source exchange condition reads the actual quotient and original low shift lengths. -/
def quotientShift (width : Nat) (enough : 2 ≤ width.size) :
    Word.ZeroTestLayout (encoding := encoding width) (2 * width.size - 2) :=
  pair width .quotient .shift (by decide) enough

/-- Read the real high-two/low-shift coordinates, in that physical semantic order. -/
def clockBit (width : Nat) (index : Fin (width.size + 2)) : EncodedBit (encoding width) :=
  if high : index.val < 2 then paddingBit width ⟨index.val, high⟩
  else shiftBit width ⟨index.val - 2, by have bound := index.isLt; omega⟩

private theorem clockBit_injective (width : Nat) :
    Function.Injective (fun index : Fin (width.size + 2) => (clockBit width index).wire) := by
  intro left right same
  change (clockBit width left).wire = (clockBit width right).wire at same
  unfold clockBit at same
  split at same <;> split at same
  · apply Fin.ext
    have values := congrArg Fin.val same
    have leftPosition := paddingBit_wire width ⟨left.val, by assumption⟩
    have rightPosition := paddingBit_wire width ⟨right.val, by assumption⟩
    have positions : width + left.val = width + right.val :=
      leftPosition.symm.trans (values.trans rightPosition)
    omega
  · exact False.elim (paddingBit_shiftBit_ne width _ _ same)
  · exact False.elim (paddingBit_shiftBit_ne width _ _ same.symm)
  · apply Fin.ext
    have values := congrArg Fin.val same
    have leftBound := left.isLt
    have rightBound := right.isLt
    have leftPosition := shiftBit_wire width ⟨left.val - 2, by omega⟩
    have rightPosition := shiftBit_wire width ⟨right.val - 2, by omega⟩
    have positions : 2 * (width + 3) + 3 * width.size + (left.val - 2) =
        2 * (width + 3) + 3 * width.size + (right.val - 2) :=
      leftPosition.symm.trans (values.trans rightPosition)
    omega

/-- Full repaired-clock zero detection uses only existing Work2 bits for its dirty chain. -/
def extendedClock (width : Nat) :
    Word.ZeroTestLayout (encoding := encoding width) width.size :=
  fromSource width width.size (by have bound := size_capacity width; omega)
    ⟨clockBit width⟩ (clockBit_injective width)
    (by
      intro index
      dsimp only
      unfold clockBit
      split
      · apply Or.inl
        rw [paddingBit_wire]
        omega
      · apply Or.inr
        rw [shiftBit_wire]
        omega)
    (by
      intro index
      dsimp only
      unfold clockBit
      split
      · rw [paddingBit_wire, controlBit_wire]
        omega
      · rw [shiftBit_wire, controlBit_wire]
        have bound := index.isLt
        omega)

/-- The extended predicate observes the actual Work1 high bits, not an extra logical register. -/
theorem extendedClock_source_get (width : Nat) (index : Fin (width.size + 2))
    (state : Registers width) :
    ((extendedClock width).source.bit index).get state =
      if index.val < 2 then
        (NumberTheory.SharedEEA.PaddingClock.high state.firstWord).getMsbD index.val
      else state.shift.getMsbD (index.val - 2) := by
  change (clockBit width index).get state = _
  unfold clockBit
  split
  · exact paddingBit_get width _ state
  · exact shiftBit_get width _ state

/-- Each borrowed work bit has its unchanged physical identity inside the existing Work2. -/
theorem workBit_placement (width count base : Nat) (capacity : count ≤ width + 3)
    (index : Fin count) :
    (qubitLayout width base).physical_idx (workBit width count capacity index).wire =
      base + (width + 3) + index.val := by
  rw [qubitLayout_bit_identity, workBit_wire]
  omega

/-- The zero-test output is the fifth allocated control, independently of any input value. -/
theorem control_placement (width base : Nat) :
    (qubitLayout width base).physical_idx (controlBit width).wire =
      base + 2 * (width + 3) + 4 * width.size + 4 := by
  rw [qubitLayout_bit_identity, controlBit_wire]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.PredicateLayout
