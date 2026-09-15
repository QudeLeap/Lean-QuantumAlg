/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Arithmetic.Selection.Predicate

/-!
# Exact finite arithmetic selector keys and their actual field decoding

A key is exactly the bit pattern read by the real equality circuit. Its
four length fields are decoded in full, including leading zeros, and
positions use Nat sums rather than wrapping length-register arithmetic
[LYL+26, sec_EEA/sub_regshare.tex:22-26,278,291;
sec_EEA/sub_opt.tex:43-48,61-66].

When Sign is omitted there is no extra phantom Sign component in the
key enumeration. Every complete frame therefore matches precisely one
key, and every such key occurs once in the fixed finite schedule. This
enumeration is a compile-time list; input values are read only by the
actual quantum predicate gates.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionKey

noncomputable section

open ArithmeticSelectionLayout ArithmeticSelectionPredicate

/-- Exactly the actual finite readout bits, with no additional unobserved key coordinates. -/
abbrev Key (width : Nat) (includeSign : Bool) := Pattern width includeSign

/-- The mathematical readout of those actual source coordinates on the complete frame. -/
def readKey (width : Nat) (includeSign : Bool) (state : Registers width) : Key width includeSign :=
  fun index => (sourceBit width includeSign index).get state

/-- The real pattern gate condition is precisely equality with the full actual readout key. -/
theorem matches_key_iff (width : Nat) (includeSign : Bool) (selected : Key width includeSign)
    (state : Registers width) :
    Matches selected state ↔ readKey width includeSign state = selected := by
  constructor
  · intro matched
    funext index
    exact matched index
  · intro same index
    exact congrFun same index

/-- No complete input can match two different fixed selector patterns. -/
theorem matches_unique (width : Nat) (includeSign : Bool) (left right : Key width includeSign)
    (state : Registers width) (first : Matches left state) (second : Matches right state) :
    left = right :=
  ((matches_key_iff width includeSign left state).mp first).symm.trans
    ((matches_key_iff width includeSign right state).mp second)

/-- The key actually read from a frame always matches its own actual source bits. -/
theorem condition_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    condition (readKey width includeSign state) state = true :=
  decide_eq_true (fun _ => rfl)

/-- Every distinct fixed key produces an inactive actual predicate on this frame. -/
theorem condition_false_of_ne (width : Nat) (includeSign : Bool)
    (selected : Key width includeSign) (state : Registers width)
    (different : selected ≠ readKey width includeSign state) :
    condition selected state = false :=
  decide_eq_false (fun matched => different
    ((matches_key_iff width includeSign selected state).mp matched).symm)

/-- Changing only the predicate output cannot alter the actual source readout. -/
theorem readKey_xorControl (width : Nat) (includeSign : Bool) (value : Bool)
    (state : Registers width) :
    readKey width includeSign (NativePredicate.xorControl value state) =
      readKey width includeSign state := by
  funext index
  change (sourceBit width includeSign index).get (NativePredicate.xorControl value state) =
    (sourceBit width includeSign index).get state
  rw [sourceBit_get, sourceBit_get]
  rfl

private def decodeWord {length : Nat} (bits : Fin length → Bool) : BitVec length :=
  (BitVec.ofBoolListBE (List.ofFn bits)).cast List.length_ofFn

private theorem decodeWord_get {length : Nat} (bits : Fin length → Bool) (index : Fin length) :
    (decodeWord bits).getMsbD index.val = bits index := by
  rw [decodeWord, BitVec.getMsbD_cast, BitVec.getMsbD_ofBoolListBE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos index.isLt]
  rfl

private def coefficientIndex (width : Nat) (includeSign : Bool) (index : Fin width.size) :
    Fin (sourceCount width includeSign) :=
  ⟨index.val, by unfold sourceCount; have within := index.isLt; omega⟩

private def quotientIndex (width : Nat) (includeSign : Bool) (index : Fin width.size) :
    Fin (sourceCount width includeSign) :=
  ⟨width.size + index.val, by unfold sourceCount; have within := index.isLt; omega⟩

private def divisorIndex (width : Nat) (includeSign : Bool) (index : Fin width.size) :
    Fin (sourceCount width includeSign) :=
  ⟨2 * width.size + index.val, by unfold sourceCount; have within := index.isLt; omega⟩

private def shiftIndex (width : Nat) (includeSign : Bool) (index : Fin width.size) :
    Fin (sourceCount width includeSign) :=
  ⟨3 * width.size + index.val, by unfold sourceCount; have within := index.isLt; omega⟩

private def firstIndex (width : Nat) (includeSign : Bool) : Fin (sourceCount width includeSign) :=
  ⟨4 * width.size, by unfold sourceCount; omega⟩

private def secondIndex (width : Nat) (includeSign : Bool) : Fin (sourceCount width includeSign) :=
  ⟨4 * width.size + 1, by unfold sourceCount; omega⟩

private def signIndex (width : Nat) : Fin (sourceCount width true) :=
  ⟨4 * width.size + 2, by simp [sourceCount]⟩

/-- Decode the complete fixed coefficient-length field without truncating a sum. -/
def coefficient {width : Nat} {includeSign : Bool} (selected : Key width includeSign) :
    BitVec width.size := decodeWord fun index => selected (coefficientIndex width includeSign index)

/-- Decode the complete fixed quotient-length field. -/
def quotient {width : Nat} {includeSign : Bool} (selected : Key width includeSign) :
    BitVec width.size := decodeWord fun index => selected (quotientIndex width includeSign index)

/-- Decode the complete divisor-length boundary for the full phase-four coefficient window. -/
def divisor {width : Nat} {includeSign : Bool} (selected : Key width includeSign) :
    BitVec width.size := decodeWord fun index => selected (divisorIndex width includeSign index)

/-- Decode the complete fixed low-shift field. -/
def shift {width : Nat} {includeSign : Bool} (selected : Key width includeSign) :
    BitVec width.size := decodeWord fun index => selected (shiftIndex width includeSign index)

/-- The first source phase is an actual key bit, not a separately supplied branch value. -/
def first {width : Nat} {includeSign : Bool} (selected : Key width includeSign) : Bool :=
  selected (firstIndex width includeSign)

/-- The second source phase is an actual key bit. -/
def second {width : Nat} {includeSign : Bool} (selected : Key width includeSign) : Bool :=
  selected (secondIndex width includeSign)

/-- Only a key whose actual readout includes Sign permits its Sign coordinate to be selected. -/
def sign {width : Nat} (selected : Key width true) : Bool := selected (signIndex width)

/-- Decoding the real coefficient-length bits recovers the original complete finite word. -/
theorem coefficient_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    coefficient (readKey width includeSign state) = state.coefficientLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [coefficient, decodeWord_get _ ⟨index, within⟩]
  change (sourceBit width includeSign (coefficientIndex width includeSign ⟨index, within⟩)).get
    state = _
  rw [sourceBit_get]
  have selected : (coefficientIndex width includeSign ⟨index, within⟩).val < width.size :=
    within
  rw [if_pos selected]
  exact congrArg state.coefficientLength.getMsbD
    (show (coefficientIndex width includeSign ⟨index, within⟩).val = index from rfl)

/-- Decoding the real quotient-length bits retains every bit of its original finite word. -/
theorem quotient_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    quotient (readKey width includeSign state) = state.quotientLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [quotient, decodeWord_get _ ⟨index, within⟩]
  change (sourceBit width includeSign (quotientIndex width includeSign ⟨index, within⟩)).get
    state = _
  rw [sourceBit_get]
  have before : ¬(quotientIndex width includeSign ⟨index, within⟩).val < width.size := by
    change ¬width.size + index < width.size
    omega
  have selected : (quotientIndex width includeSign ⟨index, within⟩).val < 2 * width.size := by
    change width.size + index < 2 * width.size
    omega
  rw [if_neg before, if_pos selected]
  change state.quotientLength.getMsbD (width.size + index - width.size) = _
  rw [Nat.add_sub_cancel_left]

/-- Decoding the divisor boundary recovers its actual complete finite field. -/
theorem divisor_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    divisor (readKey width includeSign state) = state.divisorLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [divisor, decodeWord_get _ ⟨index, within⟩]
  change (sourceBit width includeSign (divisorIndex width includeSign ⟨index, within⟩)).get
    state = _
  rw [sourceBit_get]
  have before : ¬(divisorIndex width includeSign ⟨index, within⟩).val < width.size := by
    change ¬2 * width.size + index < width.size
    omega
  have middle : ¬(divisorIndex width includeSign ⟨index, within⟩).val < 2 * width.size := by
    change ¬2 * width.size + index < 2 * width.size
    omega
  have selected : (divisorIndex width includeSign ⟨index, within⟩).val < 3 * width.size := by
    change 2 * width.size + index < 3 * width.size
    omega
  rw [if_neg before, if_neg middle, if_pos selected]
  change state.divisorLength.getMsbD (2 * width.size + index - 2 * width.size) = _
  rw [Nat.add_sub_cancel_left]

/-- Decoding the real shift bits recovers its original finite word, including width zero. -/
theorem shift_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    shift (readKey width includeSign state) = state.shift := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [shift, decodeWord_get _ ⟨index, within⟩]
  change (sourceBit width includeSign (shiftIndex width includeSign ⟨index, within⟩)).get state = _
  rw [sourceBit_get]
  have before : ¬(shiftIndex width includeSign ⟨index, within⟩).val < width.size := by
    change ¬3 * width.size + index < width.size
    omega
  have middle : ¬(shiftIndex width includeSign ⟨index, within⟩).val < 2 * width.size := by
    change ¬3 * width.size + index < 2 * width.size
    omega
  have afterDivisor : ¬(shiftIndex width includeSign ⟨index, within⟩).val < 3 * width.size := by
    change ¬3 * width.size + index < 3 * width.size
    omega
  have selected : (shiftIndex width includeSign ⟨index, within⟩).val < 4 * width.size := by
    change 3 * width.size + index < 4 * width.size
    omega
  rw [if_neg before, if_neg middle, if_neg afterDivisor, if_pos selected]
  change state.shift.getMsbD (3 * width.size + index - 3 * width.size) = _
  rw [Nat.add_sub_cancel_left]

private theorem source_after_lengths (width : Nat) (includeSign : Bool)
    (index : Fin (sourceCount width includeSign)) (later : 4 * width.size ≤ index.val)
    (state : Registers width) :
    (sourceBit width includeSign index).get state =
      if index.val = 4 * width.size then state.flags.first
      else if index.val = 4 * width.size + 1 then state.flags.second else state.flags.sign := by
  rw [sourceBit_get, if_neg (by omega : ¬index.val < width.size),
    if_neg (by omega : ¬index.val < 2 * width.size),
    if_neg (by omega : ¬index.val < 3 * width.size), if_neg (Nat.not_lt.mpr later)]

/-- The first phase read from the actual key is precisely the original phase field. -/
theorem first_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    first (readKey width includeSign state) = state.flags.first := by
  change (sourceBit width includeSign (firstIndex width includeSign)).get state = _
  rw [source_after_lengths width includeSign _ (Nat.le_refl _) state]
  have selected : (firstIndex width includeSign).val = 4 * width.size := rfl
  rw [if_pos selected]

/-- The second phase read from the actual key is precisely the original phase field. -/
theorem second_readKey (width : Nat) (includeSign : Bool) (state : Registers width) :
    second (readKey width includeSign state) = state.flags.second := by
  change (sourceBit width includeSign (secondIndex width includeSign)).get state = _
  have later : 4 * width.size ≤ (secondIndex width includeSign).val := by
    change 4 * width.size ≤ 4 * width.size + 1
    omega
  rw [source_after_lengths width includeSign _ later state]
  have notFirst : (secondIndex width includeSign).val ≠ 4 * width.size := by
    change 4 * width.size + 1 ≠ 4 * width.size
    omega
  have selected : (secondIndex width includeSign).val = 4 * width.size + 1 := rfl
  rw [if_neg notFirst, if_pos selected]

/-- Sign is recovered exactly when it is an actual source coordinate of the selector. -/
theorem sign_readKey (width : Nat) (state : Registers width) :
    sign (readKey width true state) = state.flags.sign := by
  change (sourceBit width true (signIndex width)).get state = _
  have later : 4 * width.size ≤ (signIndex width).val := by
    change 4 * width.size ≤ 4 * width.size + 2
    omega
  rw [source_after_lengths width true _ later state]
  have notFirst : (signIndex width).val ≠ 4 * width.size := by
    change 4 * width.size + 2 ≠ 4 * width.size
    omega
  have notSecond : (signIndex width).val ≠ 4 * width.size + 1 := by
    change 4 * width.size + 2 ≠ 4 * width.size + 1
    omega
  rw [if_neg notFirst, if_neg notSecond]

/-- Enumerate each complete actual key exactly once, with no unobserved Sign dimension. -/
def keys (width : Nat) (includeSign : Bool) : List (Key width includeSign) := Finset.univ.toList

/-- The compile-time key schedule has no repetitions. -/
theorem keys_nodup (width : Nat) (includeSign : Bool) : (keys width includeSign).Nodup :=
  Finset.nodup_toList _

/-- Every actual source bit pattern is present in the fixed key enumeration. -/
theorem key_mem (width : Nat) (includeSign : Bool) (selected : Key width includeSign) :
    selected ∈ keys width includeSign :=
  Finset.mem_toList.mpr (Finset.mem_univ selected)

/-- The exact schedule size is the cardinality of the actual finite source readout. -/
theorem keys_length (width : Nat) (includeSign : Bool) :
    (keys width includeSign).length = 2 ^ sourceCount width includeSign := by
  simp [keys, Key, Pattern]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ArithmeticSelectionKey
