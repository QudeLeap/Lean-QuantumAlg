/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Logic.Equiv.Fin.Basic

/-! # A complete finite coordinate bijection reflecting one prefix and retaining its complement -/

namespace QuantumAlg.Permutation

private def reflectedIndex (size count : Nat) (fits : count ≤ size) (index : Fin size) :
    Fin size :=
  if selected : index.val < count then
    ⟨count - 1 - index.val, by have := index.isLt; omega⟩ else index

private lemma reflectedIndex_value (size count : Nat) (fits : count ≤ size) (index : Fin size) :
    (reflectedIndex size count fits index).val =
      if index.val < count then count - 1 - index.val else index.val := by
  by_cases selected : index.val < count
  · simp only [reflectedIndex, dif_pos selected, if_pos selected]
  · simp only [reflectedIndex, dif_neg selected, if_neg selected]

private lemma reflectedIndex_involutive (size count : Nat) (fits : count ≤ size) :
    Function.Involutive (reflectedIndex size count fits) := by
  intro index
  apply Fin.ext
  by_cases selected : index.val < count
  · have value : (reflectedIndex size count fits index).val = count - 1 - index.val := by
      rw [reflectedIndex_value, if_pos selected]
    rw [reflectedIndex_value, value, if_pos (show count - 1 - index.val < count by omega)]
    omega
  · have value : (reflectedIndex size count fits index).val = index.val := by
      rw [reflectedIndex_value, if_neg selected]
    rw [reflectedIndex_value, value, if_neg selected]

/-- One actual coordinate permutation retains the full finite complement at its original indices. -/
def prefixReflection (size count : Nat) (fits : count ≤ size) : Equiv.Perm (Fin size) where
  toFun := reflectedIndex size count fits
  invFun := reflectedIndex size count fits
  left_inv := reflectedIndex_involutive size count fits
  right_inv := reflectedIndex_involutive size count fits

/-- Its coordinates state the full finite source placement without omitting outside positions. -/
lemma prefixReflection_value (size count : Nat) (fits : count ≤ size) (index : Fin size) :
    (prefixReflection size count fits index).val =
      if index.val < count then count - 1 - index.val else index.val :=
  reflectedIndex_value size count fits index

/-- Every declared coordinate outside the reflected prefix remains at its original position. -/
lemma prefixReflection_outside (size count : Nat) (fits : count ≤ size) (index : Fin size)
    (outside : count ≤ index.val) : prefixReflection size count fits index = index := by
  apply Fin.ext
  rw [prefixReflection_value, if_neg (by omega)]

end QuantumAlg.Permutation
