/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Window.Chronology
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact total width and amplitude products of recycled windows

Every complete logical window has the configured width and the possible
high tail has precisely the remainder. Chronological reversal preserves the
sum and the corresponding product of powers. All statements keep the total
width and positive window width symbolic.
-/

namespace QuantumAlg.Nat.FixedWidth.Window.Chronology

open scoped BigOperators

private lemma full_width_sum (totalBits windowWidth : Nat) :
    (∑ index : Fin (totalBits / windowWidth),
      activeWidth totalBits windowWidth index.val) =
        (totalBits / windowWidth) * windowWidth := by
  have terms (index : Fin (totalBits / windowWidth)) :
      activeWidth totalBits windowWidth index.val = windowWidth := activeWidth_full index.isLt
  simp only [terms, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]

/-- The logical active windows contain every original bit exactly once in total width. -/
lemma activeWidth_sum (totalBits windowWidth : Nat) (positive : 0 < windowWidth) :
    (∑ index : Fin (windowCount totalBits windowWidth),
      activeWidth totalBits windowWidth index.val) = totalBits := by
  have decomposition := Nat.mod_add_div totalBits windowWidth
  by_cases exactWidth : totalBits % windowWidth = 0
  · rw [windowCount_of_remainder_zero exactWidth, full_width_sum, Nat.mul_comm]
    omega
  · rw [windowCount_of_remainder_ne_zero exactWidth, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [full_width_sum, activeWidth_tail totalBits windowWidth positive, Nat.mul_comm]
    omega

/-- Executing the high tail first and then descending windows preserves the exact total width. -/
lemma chronological_activeWidth_sum (totalBits windowWidth : Nat)
    (positive : 0 < windowWidth) :
    (∑ position : Fin (windowCount totalBits windowWidth),
      activeWidth totalBits windowWidth
        (logical (windowCount totalBits windowWidth) position).val) = totalBits :=
  (Equiv.sum_comp (logical (windowCount totalBits windowWidth))
    (fun index => activeWidth totalBits windowWidth index.val)).trans
      (activeWidth_sum totalBits windowWidth positive)

/-- Every actual logical window amplitude contributes its full width to the same base power. -/
lemma activeWidth_pow_product {M : Type} [CommMonoid M] (amplitude : M)
    (totalBits windowWidth : Nat) (positive : 0 < windowWidth) :
    (∏ index : Fin (windowCount totalBits windowWidth),
      amplitude ^ activeWidth totalBits windowWidth index.val) = amplitude ^ totalBits := by
  rw [Finset.prod_pow_eq_pow_sum, activeWidth_sum totalBits windowWidth positive]

/-- The actual high-first schedule has the same exact amplitude normalization exponent. -/
lemma chronological_activeWidth_pow_product {M : Type} [CommMonoid M] (amplitude : M)
    (totalBits windowWidth : Nat) (positive : 0 < windowWidth) :
    (∏ position : Fin (windowCount totalBits windowWidth),
      amplitude ^ activeWidth totalBits windowWidth
        (logical (windowCount totalBits windowWidth) position).val) = amplitude ^ totalBits := by
  rw [Finset.prod_pow_eq_pow_sum, chronological_activeWidth_sum totalBits windowWidth positive]

end QuantumAlg.Nat.FixedWidth.Window.Chronology
