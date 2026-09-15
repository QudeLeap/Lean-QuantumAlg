/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.BitVec

/-!
# Exact unrotated shared-EEA word encodings

The source stores the coefficient at the left in little-endian order,
followed by an explicit zero bit, the effective quotient in big-endian
order, and the remainder in big-endian order
[LYL+26, sec_EEA/sub_regshare.tex:16-17]. The second word places its
little-endian coefficient before its big-endian remainder
[LYL+26, sec_EEA/sub_regshare.tex:19-20].

These definitions encode exactly those ordered bit segments and decode
them by their actual length boundaries. Both encodings have proved left
inverses and explicit wire-bit equations. Zero-length segments are allowed.
The widths are supplied by the source length coordinates; this module
does not infer an encoding from cardinality or truncate an unbounded input.

Choosing the phase-dependent lengths inside the source's `n+3` words and
proving all rotated intermediate encodings are subsequent obligations.
This module establishes the exact unrotated bit representation that those
proofs must preserve.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.WordPacking

variable {coefficientWidth quotientWidth remainderWidth : Nat}

/-- The three bounded logical segments of the first shared source word. -/
@[ext]
structure Work1Payload (coefficientWidth quotientWidth remainderWidth : Nat) where
  coefficientBits : BitVec coefficientWidth
  quotientBits : BitVec quotientWidth
  remainderBits : BitVec remainderWidth
deriving DecidableEq

/-- The first word's literal bit layout, including the prescribed coefficient zero bit. -/
def packWork1 (payload : Work1Payload coefficientWidth quotientWidth remainderWidth) :
    BitVec ((coefficientWidth + 1) + (quotientWidth + remainderWidth)) :=
  (payload.coefficientBits.reverse ++ (0 : BitVec 1)) ++
    (payload.quotientBits ++ payload.remainderBits)

/-- Read the exact source boundaries and restore the coefficient's logical bit order. -/
def unpackWork1
    (word : BitVec ((coefficientWidth + 1) + (quotientWidth + remainderWidth))) :
    Work1Payload coefficientWidth quotientWidth remainderWidth :=
  let head := word.extractLsb' (quotientWidth + remainderWidth) (coefficientWidth + 1)
  let tail := word.extractLsb' 0 (quotientWidth + remainderWidth)
  ⟨(head.extractLsb' 1 coefficientWidth).reverse,
    tail.extractLsb' remainderWidth quotientWidth, tail.extractLsb' 0 remainderWidth⟩

/-- The actual first-word bits recover every bounded logical segment exactly. -/
theorem unpackWork1_packWork1
    (payload : Work1Payload coefficientWidth quotientWidth remainderWidth) :
    unpackWork1 (packWork1 payload) = payload := by
  apply Work1Payload.ext
  · simp only [unpackWork1, packWork1, BitVec.extractLsb'_append_eq_left,
      BitVec.reverse_reverse_eq]
  · simp only [unpackWork1, packWork1, BitVec.extractLsb'_append_eq_right,
      BitVec.extractLsb'_append_eq_left]
  · simp only [unpackWork1, packWork1, BitVec.extractLsb'_append_eq_right]

/-- Distinct bounded first-word payloads have distinct literal bit encodings. -/
theorem packWork1_injective :
    Function.Injective (packWork1 (coefficientWidth := coefficientWidth)
      (quotientWidth := quotientWidth) (remainderWidth := remainderWidth)) := by
  intro left right same
  calc
    left = unpackWork1 (packWork1 left) := (unpackWork1_packWork1 left).symm
    _ = unpackWork1 (packWork1 right) := congrArg unpackWork1 same
    _ = right := unpackWork1_packWork1 right

/-- Physical bits at the left read the coefficient from least to most significant. -/
theorem packWork1_coefficient_bit
    (payload : Work1Payload coefficientWidth quotientWidth remainderWidth)
    (index : Nat) (within : index < coefficientWidth) :
    (packWork1 payload).getMsbD index = payload.coefficientBits.getLsbD index := by
  have beforeHead : ¬ coefficientWidth + 1 ≤ index := by omega
  have beforeCoefficient : ¬ coefficientWidth ≤ index := by omega
  simp only [packWork1, BitVec.getMsbD_append, if_neg beforeHead, if_neg beforeCoefficient,
    BitVec.getMsbD_reverse]

/-- The prescribed bit immediately after the coefficient is actually zero. -/
theorem packWork1_separator
    (payload : Work1Payload coefficientWidth quotientWidth remainderWidth) :
    (packWork1 payload).getMsbD coefficientWidth = false := by
  simp [packWork1]

/-- The middle physical segment reads the effective quotient in big-endian order. -/
theorem packWork1_quotient_bit
    (payload : Work1Payload coefficientWidth quotientWidth remainderWidth)
    (index : Nat) (within : index < quotientWidth) :
    (packWork1 payload).getMsbD (coefficientWidth + 1 + index) =
      payload.quotientBits.getMsbD index := by
  have afterHead : coefficientWidth + 1 ≤ coefficientWidth + 1 + index := by omega
  have withinQuotient : ¬ quotientWidth ≤ index := by omega
  simp only [packWork1, BitVec.getMsbD_append, if_pos afterHead, Nat.add_sub_cancel_left,
    if_neg withinQuotient]

/-- The right physical segment reads the remainder in big-endian order. -/
theorem packWork1_remainder_bit
    (payload : Work1Payload coefficientWidth quotientWidth remainderWidth) (index : Nat) :
    (packWork1 payload).getMsbD (coefficientWidth + 1 + quotientWidth + index) =
      payload.remainderBits.getMsbD index := by
  have afterHead : coefficientWidth + 1 ≤ coefficientWidth + 1 + quotientWidth + index := by omega
  have offset : coefficientWidth + 1 + quotientWidth + index - (coefficientWidth + 1) =
      quotientWidth + index := by omega
  have afterQuotient : quotientWidth ≤ quotientWidth + index := by omega
  simp only [packWork1, BitVec.getMsbD_append, if_pos afterHead, offset, if_pos afterQuotient,
    Nat.add_sub_cancel_left]

/-- The two bounded segments of the unrotated second shared source word. -/
@[ext]
structure Work2Payload (coefficientWidth remainderWidth : Nat) where
  coefficientBits : BitVec coefficientWidth
  remainderBits : BitVec remainderWidth
deriving DecidableEq

/-- The unrotated second word's literal opposite-endian segment layout. -/
def packWork2 (payload : Work2Payload coefficientWidth remainderWidth) :
    BitVec (coefficientWidth + remainderWidth) :=
  payload.coefficientBits.reverse ++ payload.remainderBits

/-- Decode the actual remainder boundary and restore coefficient bit order. -/
def unpackWork2 (word : BitVec (coefficientWidth + remainderWidth)) :
    Work2Payload coefficientWidth remainderWidth :=
  ⟨(word.extractLsb' remainderWidth coefficientWidth).reverse,
    word.extractLsb' 0 remainderWidth⟩

/-- The second-word bit layout also has an exact left inverse. -/
theorem unpackWork2_packWork2 (payload : Work2Payload coefficientWidth remainderWidth) :
    unpackWork2 (packWork2 payload) = payload := by
  apply Work2Payload.ext
  · simp only [unpackWork2, packWork2, BitVec.extractLsb'_append_eq_left,
      BitVec.reverse_reverse_eq]
  · simp only [unpackWork2, packWork2, BitVec.extractLsb'_append_eq_right]

/-- Distinct second-word logical values remain distinguishable in the actual bits. -/
theorem packWork2_injective :
    Function.Injective (packWork2 (coefficientWidth := coefficientWidth)
      (remainderWidth := remainderWidth)) := by
  intro left right same
  calc
    left = unpackWork2 (packWork2 left) := (unpackWork2_packWork2 left).symm
    _ = unpackWork2 (packWork2 right) := congrArg unpackWork2 same
    _ = right := unpackWork2_packWork2 right

/-- The second word's left physical segment has the source's little-endian coefficient. -/
theorem packWork2_coefficient_bit (payload : Work2Payload coefficientWidth remainderWidth)
    (index : Nat) (within : index < coefficientWidth) :
    (packWork2 payload).getMsbD index = payload.coefficientBits.getLsbD index := by
  simp only [packWork2, BitVec.getMsbD_append, if_neg (Nat.not_le_of_lt within),
    BitVec.getMsbD_reverse]

/-- Its right physical segment retains the source's big-endian remainder. -/
theorem packWork2_remainder_bit (payload : Work2Payload coefficientWidth remainderWidth)
    (index : Nat) :
    (packWork2 payload).getMsbD (coefficientWidth + index) =
      payload.remainderBits.getMsbD index := by
  simp only [packWork2, BitVec.getMsbD_append, if_pos (Nat.le_add_right coefficientWidth index),
    Nat.add_sub_cancel_left]

/-- Empty effective segments still retain the one explicitly prescribed separator bit. -/
theorem empty_work1_payload :
    packWork1 (⟨0, 0, 0⟩ : Work1Payload 0 0 0) = (0 : BitVec 1) := by decide

/-- The smallest modulus uses the source's literal five-bit initial first word. -/
theorem smallest_initial_work1 :
    packWork1 (⟨1, 0, 2⟩ : Work1Payload 1 0 3) = (18 : BitVec 5) := by decide

end QuantumAlg.NumberTheory.SharedEEA.WordPacking
