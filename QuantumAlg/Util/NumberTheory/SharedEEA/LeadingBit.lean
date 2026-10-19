/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

/-!
# Exact leading-bit characterization of the initial divisor length

The input-dependent length in [LYL+26, sec_EEA/sub_4phase.tex:108-117]
is the ordinary binary length of the current divisor. Reading zero before
one in the physical most-significant-first order determines that length
uniquely. This is a finite-bit arithmetic statement, independent of any
quantum implementation or promise that a length register is initially zero.

The zero input has no selected leading position. Width zero is covered by
the empty position type. The finite encoding of every resulting length fits
in `Nat.size width` bits, including the zero-width boundary. A concrete
folded original-domain example records why the length must be computed after
folding, rather than retained from the unfurled input.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.LeadingBit

/-- A most-significant-first position with zero bits before it and a one at that position. -/
def selected (width value : Nat) (index : Fin width) : Prop :=
  (∀ previous : Fin index.val, value.testBit (width - 1 - previous.val) = false) ∧
    value.testBit (width - 1 - index.val) = true

/-- The selected position is exactly the finite word's ordinary binary length. -/
lemma selected_iff_size (width value : Nat) (fits : value < 2 ^ width) (index : Fin width) :
    selected width value index ↔ value.size = width - index.val := by
  have indexBound := index.isLt
  let exponent := width - 1 - index.val
  have exponentBound : exponent < width := by dsimp [exponent]; omega
  constructor
  · rintro ⟨zeros, one⟩
    have lower : exponent < value.size := Nat.lt_size.mpr (Nat.ge_two_pow_of_testBit one)
    have upper : value.size ≤ exponent + 1 := by
      apply Nat.size_le.mpr
      apply Nat.lt_pow_two_of_testBit
      intro position above
      by_cases inside : position < width
      · let earlier : Fin index.val := ⟨width - 1 - position, by
          dsimp only [exponent] at above
          omega⟩
        have zero := zeros earlier
        have recover : width - 1 - earlier.val = position := by
          dsimp [earlier]
          omega
        rw [recover] at zero
        exact zero
      · exact Nat.testBit_lt_two_pow
          (fits.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    dsimp only [exponent] at lower upper
    omega
  · intro length
    have sizeExact : value.size = exponent + 1 := by dsimp [exponent]; omega
    constructor
    · intro previous
      have previousBound := previous.isLt
      apply Nat.testBit_lt_two_pow
      apply (Nat.lt_size_self value).trans_le
      apply Nat.pow_le_pow_right (by decide)
      omega
    · apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
      · apply Nat.lt_size.mp
        omega
      · have bound := Nat.lt_size_self value
        simpa only [sizeExact] using bound

/-- There is at most one leading-one position, also for zero-valued inputs. -/
lemma selected_unique (width value : Nat) (fits : value < 2 ^ width)
    (left right : Fin width) (leftSelected : selected width value left)
    (rightSelected : selected width value right) : left = right := by
  have first := (selected_iff_size width value fits left).mp leftSelected
  have second := (selected_iff_size width value fits right).mp rightSelected
  apply Fin.ext
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

/-- A positive finite value supplies its actual physical leading index. -/
def index (width value : Nat) (fits : value < 2 ^ width) (positive : 0 < value) : Fin width :=
  ⟨width - value.size, by
    have lengthBound := Nat.size_le.mpr fits
    have lengthPositive := Nat.size_pos.mpr positive
    omega⟩

lemma index_selected (width value : Nat) (fits : value < 2 ^ width) (positive : 0 < value) :
    selected width value (index width value fits positive) := by
  apply (selected_iff_size width value fits _).mpr
  change value.size = width - (width - value.size)
  have lengthBound := Nat.size_le.mpr fits
  omega

/-- Zero has no leading one; it therefore writes no length bit in the position-based circuit. -/
lemma zero_not_selected (width : Nat) (position : Fin width) :
    ¬selected width 0 position := by
  intro chosen
  have impossible := chosen.2
  simp only [Nat.zero_testBit, Bool.false_eq_true] at impossible

/-- The exact ordinary binary length fits in the source's existing finite length field. -/
lemma encoded_length_fits (width value : Nat) (fits : value < 2 ^ width) :
    value.size < 2 ^ width.size :=
  (Nat.size_le.mpr fits).trans_lt (Nat.lt_size_self width)

/-- The displayed source order would retain length five after folding sixteen to one. -/
lemma folded_seventeen_sixteen_lengths :
    0 < (16 : Nat) ∧ 16 < 17 ∧ 17 / 2 < 16 ∧
      (16 : Nat).size = 5 ∧ ((17 : Nat) - 16).size = 1 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.LeadingBit
