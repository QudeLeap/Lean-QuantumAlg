/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Tactic

/-!
# Finite difference, borrow and exact natural clipping

These pure identities describe the actual native difference readouts.
They do not construct a program from a boundary or first-one value.
Native preparation, physical range flags, copying and cleanup have
separate implementation obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

/-- Independent natural representative of one fixed-capacity modular subtraction. -/
def wrappedDifference (capacity left right : Nat) : Nat :=
  (left + capacity - right) % capacity

/-- On the no-borrow branch the actual finite difference is the complete natural difference. -/
lemma wrappedDifference_of_le (capacity left right : Nat) (fits : left < capacity)
    (noBorrow : right ≤ left) : wrappedDifference capacity left right = left - right := by
  have expression : left + capacity - right = capacity + (left - right) := by omega
  have difference : left - right < capacity := lt_of_le_of_lt (Nat.sub_le _ _) fits
  simp only [wrappedDifference, expression, Nat.add_mod, Nat.mod_self, Nat.zero_add,
    Nat.mod_eq_of_lt difference]

/-- No-borrow selection handles equality by copying zero and preserves the final output modulus. -/
lemma copiedDifference (capacity outputCapacity left right : Nat) (active : Bool)
    (fits : left < capacity) :
    (if active && !(decide (left < right)) then
      wrappedDifference capacity left right % outputCapacity else 0) =
        if active then (left - right) % outputCapacity else 0 := by
  by_cases borrowed : left < right
  · have zero : left - right = 0 := Nat.sub_eq_zero_of_le borrowed.le
    simp only [borrowed, decide_true, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      if_false, zero, Nat.zero_mod]
    cases active <;> rfl
  · have exactDifference := wrappedDifference_of_le capacity left right fits (by omega)
    simp only [borrowed, decide_false, Bool.not_false, Bool.and_true, exactDifference]

/-- In a narrow source region the high native length bit detects exactly the invalid boundary. -/
lemma narrow_invalid (capacity boundary key : Nat) (positive : 0 < capacity)
    (boundaryFits : boundary < capacity) (keyFits : key < capacity) :
    capacity ≤ wrappedDifference (2 * capacity) boundary key ↔ boundary < key := by
  by_cases invalid : boundary < key
  · have rawFits : boundary + 2 * capacity - key < 2 * capacity := by omega
    have high : capacity ≤ boundary + 2 * capacity - key := by omega
    simp only [wrappedDifference, Nat.mod_eq_of_lt rawFits, high, invalid]
  · have fits : boundary < 2 * capacity := by omega
    rw [wrappedDifference_of_le _ _ _ fits (by omega)]
    have low : boundary - key < capacity := lt_of_le_of_lt (Nat.sub_le _ _) boundaryFits
    omega

/-- Low-word native arithmetic plus the actual high-bit validity flag gives natural clipping. -/
lemma narrow_copy (capacity boundary key first : Nat) (control : Bool)
    (positive : 0 < capacity) (boundaryFits : boundary < capacity)
    (keyFits : key < capacity) :
    (if (control && !(decide (capacity ≤ wrappedDifference (2 * capacity) boundary key))) &&
        !(decide (wrappedDifference (2 * capacity) boundary key % capacity < first)) then
      wrappedDifference capacity
        (wrappedDifference (2 * capacity) boundary key % capacity) first % capacity
    else 0) = if control then (boundary - key - first) % capacity else 0 := by
  by_cases invalid : boundary < key
  · have high := (narrow_invalid capacity boundary key positive boundaryFits keyFits).mpr invalid
    have empty : boundary - key = 0 := Nat.sub_eq_zero_of_le invalid.le
    simp only [high, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.false_eq_true, if_false, empty, Nat.zero_sub, Nat.zero_mod]
    cases control <;> rfl
  · have full := wrappedDifference_of_le (2 * capacity) boundary key
      (by omega) (by omega)
    have fits : boundary - key < capacity := lt_of_le_of_lt (Nat.sub_le _ _) boundaryFits
    have low : ¬capacity ≤ boundary - key := by omega
    rw [full, Nat.mod_eq_of_lt fits]
    simp only [low, decide_false, Bool.not_false, Bool.and_true]
    exact copiedDifference capacity capacity (boundary - key) first control fits

/-- The wide-region case admits every finite key, so it needs no spare high-bit latch. -/
lemma wide_all_valid (capacity systems key : Nat) (wide : capacity ≤ systems)
    (keyFits : key < capacity) : key ≤ systems - 1 := by omega

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
