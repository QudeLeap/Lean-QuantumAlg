/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! # Logical unsigned windows and high-to-low chronological positions -/

namespace QuantumAlg.Nat.FixedWidth.Window.Chronology

/-- Number of complete windows and, when present, one shorter high window. -/
def windowCount (totalBits windowWidth : Nat) : Nat :=
  totalBits / windowWidth + if totalBits % windowWidth = 0 then 0 else 1

/-- Width of the logical window, whose original low bit is `windowWidth * logical`. -/
def activeWidth (totalBits windowWidth logical : Nat) : Nat :=
  min windowWidth (totalBits - windowWidth * logical)

/-- The original little-endian bit position does not depend on execution chronology. -/
def bitPosition (windowWidth logical bit : Nat) : Nat := windowWidth * logical + bit

lemma windowCount_zero (windowWidth : Nat) : windowCount 0 windowWidth = 0 := by
  simp only [windowCount, Nat.zero_div, Nat.zero_mod, ↓reduceIte, Nat.add_zero]

lemma windowCount_of_remainder_zero {totalBits windowWidth : Nat}
    (exactWidth : totalBits % windowWidth = 0) :
    windowCount totalBits windowWidth = totalBits / windowWidth := by
  simp only [windowCount, exactWidth, ↓reduceIte, Nat.add_zero]

lemma windowCount_of_remainder_ne_zero {totalBits windowWidth : Nat}
    (tail : totalBits % windowWidth ≠ 0) :
    windowCount totalBits windowWidth = totalBits / windowWidth + 1 := by
  simp only [windowCount, tail, ↓reduceIte]

lemma activeWidth_tail (totalBits windowWidth : Nat) (positive : 0 < windowWidth) :
    activeWidth totalBits windowWidth (totalBits / windowWidth) =
      totalBits % windowWidth := by
  have decomposition := Nat.mod_add_div totalBits windowWidth
  have remainder := Nat.mod_lt totalBits positive
  simp only [activeWidth]
  have remaining : totalBits - windowWidth * (totalBits / windowWidth) =
      totalBits % windowWidth := by omega
  rw [remaining, Nat.min_eq_right (Nat.le_of_lt remainder)]

/-- Every logical window before the quotient position has the complete configured width. -/
lemma activeWidth_full {totalBits windowWidth logical : Nat}
    (earlier : logical < totalBits / windowWidth) :
    activeWidth totalBits windowWidth logical = windowWidth := by
  have decomposition := Nat.mod_add_div totalBits windowWidth
  have product : windowWidth * (logical + 1) ≤
      windowWidth * (totalBits / windowWidth) :=
    Nat.mul_le_mul_left windowWidth (Nat.succ_le_of_lt earlier)
  rw [Nat.mul_add, Nat.mul_one] at product
  exact Nat.min_eq_left (by omega)

lemma activeWidth_le (totalBits windowWidth logical : Nat) :
    activeWidth totalBits windowWidth logical ≤ windowWidth := Nat.min_le_left _ _

lemma activeWidth_positive {totalBits windowWidth : Nat} (positive : 0 < windowWidth)
    (window : Fin (windowCount totalBits windowWidth)) :
    0 < activeWidth totalBits windowWidth window.val := by
  by_cases full : window.val < totalBits / windowWidth
  · rw [activeWidth_full full]
    exact positive
  · have within := window.isLt
    have tail : totalBits % windowWidth ≠ 0 := by
      intro zero
      exact full (within.trans_eq (windowCount_of_remainder_zero zero))
    have lastBound := within.trans_eq (windowCount_of_remainder_ne_zero tail)
    have last : window.val = totalBits / windowWidth := by omega
    rw [last, activeWidth_tail totalBits windowWidth positive]
    omega

/-- Each active digit bit is an original exponent bit, including a shorter high tail. -/
lemma bitPosition_lt {totalBits windowWidth logical bit : Nat}
    (active : bit < activeWidth totalBits windowWidth logical) :
    bitPosition windowWidth logical bit < totalBits := by
  have remaining := Nat.min_le_right windowWidth (totalBits - windowWidth * logical)
  change bit < min windowWidth (totalBits - windowWidth * logical) at active
  unfold bitPosition
  omega

/-- The shorter high window is the first chronological position. -/
def logical (count : Nat) : Equiv.Perm (Fin count) := Fin.revPerm

lemma logical_val (count : Nat) (position : Fin count) :
    (logical count position).val = count - (position.val + 1) := rfl

lemma logical_logical (count : Nat) (position : Fin count) :
    logical count (logical count position) = position := Fin.rev_rev position

lemma logical_first (count : Nat) :
    logical (count + 1) 0 = Fin.last count := by
  apply Fin.ext
  simp only [logical_val, Fin.val_zero, Fin.val_last]
  omega

lemma logical_last (count : Nat) :
    logical (count + 1) (Fin.last count) = 0 := by
  apply Fin.ext
  simp only [logical_val, Fin.val_last, Fin.val_zero]
  omega

/-- Reverse logical windows inside each stream, without exchanging the two streams. -/
def paired (count : Nat) : Equiv.Perm (Fin (count + count)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (logical count) (logical count)).trans finSumFinEquiv)

lemma paired_first (count : Nat) (position : Fin count) :
    paired count (position.castAdd count) = (logical count position).castAdd count := by
  simp only [paired, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

lemma paired_second (count : Nat) (position : Fin count) :
    paired count (position.natAdd count) = (logical count position).natAdd count := by
  simp only [paired, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

lemma paired_paired (count : Nat) (position : Fin (count + count)) :
    paired count (paired count position) = position := by
  refine Fin.addCases ?_ ?_ position
  · intro index
    rw [paired_first, paired_first, logical_logical]
  · intro index
    rw [paired_second, paired_second, logical_logical]

end QuantumAlg.Nat.FixedWidth.Window.Chronology
