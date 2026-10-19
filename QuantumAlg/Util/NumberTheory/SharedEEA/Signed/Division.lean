/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Packing

/-!
# Actual signed subtraction, add-back, and quotient-bit exchange

The source extracts a quotient bit by subtracting into the extended sign
word, conditionally adding the divisor back to the low word, complementing
`Sign`, and swapping it with the new quotient position
[LYL+26, sec_EEA/sub_regshare.tex:279-287]. This module uses literal `BitVec`
subtraction, addition, sign extraction, and bit concatenation for those
operations. The retained next quotient bit reconstructs the input word.

The old remainder occupies one more bit than the next remainder region.
It must not be truncated before subtraction: the valid prime example
`p = 29, x = 3` reaches old remainder five with a two-bit next remainder
region. Only the corrected result must fit that next region; its old
highest bit is then zero, so the actual swap clears `Sign`. That condition
is an internal next-state capacity fact, not an extra original input-domain
condition. The generic word laws include zero-bit remainder regions.

Connecting the source's dynamically selected widths and aligned thresholds
to these concrete instructions remains distinct from the generic word laws.
No quantum circuit, cost, or completed whole EEA implementation is asserted.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedDivision

variable {width : Nat}

/-- Subtract the two old-width words with an actual leading zero sign bit. -/
def difference (value threshold : BitVec width) : BitVec (width + 1) :=
  value.setWidth (width + 1) - threshold.setWidth (width + 1)

/-- The actual high subtraction bit is exactly unsigned underflow, including equality. -/
lemma difference_sign (value threshold : BitVec width) :
    (difference value threshold).msb = decide (value.toNat < threshold.toNat) := by
  have valueNat : (value.setWidth (width + 1)).toNat = value.toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  have thresholdNat : (threshold.setWidth (width + 1)).toNat = threshold.toNat :=
    BitVec.toNat_setWidth_of_le (by omega)
  have valueBound := value.isLt
  have thresholdBound := threshold.isLt
  change (value.setWidth (width + 1) - threshold.setWidth (width + 1)).msb = _
  rw [BitVec.msb_eq_decide, Nat.add_sub_cancel]
  by_cases borrowed : value.toNat < threshold.toNat
  · have ordered : value.setWidth (width + 1) < threshold.setWidth (width + 1) := by
      simpa only [BitVec.lt_def, valueNat, thresholdNat] using borrowed
    rw [BitVec.toNat_sub_of_lt ordered, valueNat, thresholdNat, Nat.pow_succ]
    have negative : 2 ^ width ≤ 2 ^ width * 2 - (threshold.toNat - value.toNat) := by omega
    simp [borrowed, negative]
  · have ordered : threshold.setWidth (width + 1) ≤ value.setWidth (width + 1) := by
      rw [BitVec.le_def, valueNat, thresholdNat]
      omega
    rw [BitVec.toNat_sub_of_le ordered, valueNat, thresholdNat]
    have nonnegative : ¬ 2 ^ width ≤ value.toNat - threshold.toNat := by omega
    simp [borrowed, nonnegative]

/-- Extracting the actual low subtraction bits agrees with old-width modular subtraction. -/
lemma difference_low (value threshold : BitVec width) :
    (difference value threshold).setWidth width = value - threshold := by
  unfold difference
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (by omega),
    BitVec.setWidth_neg_of_le (by omega),
    BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, BitVec.setWidth_eq,
    ← BitVec.sub_eq_add_neg]

/-- Conditionally add back on the actual subtraction sign, leaving that sign retained. -/
def corrected (value threshold : BitVec width) : BitVec width :=
  let subtracted := difference value threshold
  let low := subtracted.setWidth width
  if subtracted.msb then low + threshold else low

/-- Actual subtraction and conditional add-back implement the source's weak comparison branch. -/
lemma corrected_eq (value threshold : BitVec width) :
    corrected value threshold =
      if threshold.toNat ≤ value.toNat then value - threshold else value := by
  dsimp only [corrected]
  rw [difference_sign, difference_low]
  by_cases selected : threshold.toNat ≤ value.toNat
  · have notBorrowed : ¬ value.toNat < threshold.toNat := by omega
    simp [selected, notBorrowed]
  · have borrowed : value.toNat < threshold.toNat := by omega
    simp [selected, borrowed]

/-- The concrete word instructions compute the exact next natural remainder. -/
lemma corrected_toNat (value threshold : BitVec width) :
    (corrected value threshold).toNat =
      if threshold.toNat ≤ value.toNat then value.toNat - threshold.toNat else value.toNat := by
  rw [corrected_eq]
  by_cases selected : threshold.toNat ≤ value.toNat
  · rw [if_pos selected, if_pos selected]
    exact BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def] using selected)
  · simp only [if_neg selected]

/-- Complement the borrow bit, then swap it with the corrected old remainder's highest bit. -/
def extract (value threshold : BitVec (width + 1)) : Bool × BitVec (width + 1) :=
  let restored := corrected value threshold
  (restored.msb, BitVec.cons (!(difference value threshold).msb) (restored.setWidth width))

/-- Next-state capacity makes the physical swap clear Sign and retain the actual quotient bit. -/
lemma extract_spec (value threshold : BitVec (width + 1))
    (nextFits : (if threshold.toNat ≤ value.toNat then value.toNat - threshold.toNat
      else value.toNat) < 2 ^ width) :
    (extract value threshold).1 = false ∧
      (extract value threshold).2.msb = decide (threshold.toNat ≤ value.toNat) ∧
      ((extract value threshold).2.setWidth width).toNat =
        if threshold.toNat ≤ value.toNat then value.toNat - threshold.toNat else value.toNat := by
  have restoredFits : (corrected value threshold).toNat < 2 ^ width := by
    simpa only [corrected_toNat] using nextFits
  refine ⟨?_, ?_, ?_⟩
  · change (corrected value threshold).msb = false
    rw [BitVec.msb_eq_decide, Nat.add_sub_cancel]
    simp only [Nat.not_le.mpr restoredFits, decide_false]
  · change (BitVec.cons (!(difference value threshold).msb)
      ((corrected value threshold).setWidth width)).msb = _
    rw [BitVec.msb_cons, difference_sign]
    by_cases selected : threshold.toNat ≤ value.toNat
    · have notBorrowed : ¬ value.toNat < threshold.toNat := by omega
      simp [selected, notBorrowed]
    · have borrowed : value.toNat < threshold.toNat := by omega
      simp [selected, borrowed]
  · change ((BitVec.cons (!(difference value threshold).msb)
      ((corrected value threshold).setWidth width)).setWidth width).toNat = _
    rw [BitVec.setWidth_cons, BitVec.toNat_setWidth, Nat.mod_eq_of_lt restoredFits]
    exact corrected_toNat value threshold

/-- Read the written quotient bit and add its contribution back to reconstruct the old word. -/
def rewind (threshold : BitVec (width + 1)) (output : Bool × BitVec (width + 1)) :
    BitVec (width + 1) :=
  let remainder := (output.2.setWidth width).setWidth (width + 1)
  if output.2.msb then remainder + threshold else remainder

/-- The actual output word reconstructs the old remainder without an external branch witness. -/
lemma rewind_extract (value threshold : BitVec (width + 1))
    (nextFits : (if threshold.toNat ≤ value.toNat then value.toNat - threshold.toNat
      else value.toNat) < 2 ^ width) :
    rewind threshold (extract value threshold) = value := by
  obtain ⟨_, digit, remainder⟩ := extract_spec value threshold nextFits
  have restoredNat : (((extract value threshold).2.setWidth width).setWidth
      (width + 1)).toNat =
      if threshold.toNat ≤ value.toNat then value.toNat - threshold.toNat else value.toNat := by
    rw [BitVec.toNat_setWidth_of_le (by omega)]
    exact remainder
  apply BitVec.eq_of_toNat_eq
  unfold rewind
  rw [digit]
  by_cases selected : threshold.toNat ≤ value.toNat
  · simp only [selected, decide_true, if_true]
    rw [BitVec.toNat_add, restoredNat, if_pos selected, Nat.sub_add_cancel selected,
      Nat.mod_eq_of_lt value.isLt]
  · simp only [selected, decide_false, Bool.false_eq_true, if_false]
    simpa only [if_neg selected] using restoredNat

/-- Distinct reachable old remainder words are never merged by the actual quotient extraction. -/
lemma extract_injective (threshold : BitVec (width + 1))
    {left right : BitVec (width + 1)}
    (leftFits : (if threshold.toNat ≤ left.toNat then left.toNat - threshold.toNat
      else left.toNat) < 2 ^ width)
    (rightFits : (if threshold.toNat ≤ right.toNat then right.toNat - threshold.toNat
      else right.toNat) < 2 ^ width)
    (same : extract left threshold = extract right threshold) : left = right := by
  calc
    left = rewind threshold (extract left threshold) :=
      (rewind_extract left threshold leftFits).symm
    _ = rewind threshold (extract right threshold) := congrArg (rewind threshold) same
    _ = right := rewind_extract right threshold rightFits

/-- The valid prime boundary keeps the old high remainder bit until after subtraction. -/
lemma prime_twenty_nine_last_digit :
    difference (5 : BitVec 3) (3 : BitVec 3) = (2 : BitVec 4) ∧
      corrected (5 : BitVec 3) (3 : BitVec 3) = (2 : BitVec 3) ∧
      extract (5 : BitVec 3) (3 : BitVec 3) = (false, (6 : BitVec 3)) ∧
      rewind (3 : BitVec 3) (false, (6 : BitVec 3)) = (5 : BitVec 3) := by
  decide

/-- Equality writes quotient one and resets the remainder even when its field has zero bits. -/
lemma zero_width_equality :
    extract (1 : BitVec 1) (1 : BitVec 1) = (false, (1 : BitVec 1)) ∧
      ((extract (1 : BitVec 1) (1 : BitVec 1)).2.setWidth 0) = (0 : BitVec 0) := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.SignedDivision
