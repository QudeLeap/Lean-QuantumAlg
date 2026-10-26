/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# Canonical reduction for a modulus just below a binary capacity

These identities describe the actual carry and cleanup predicates needed by
quantum modular addition and doubling. The formulas concern all canonical
residues, including zero, and do not assume an invertible arithmetic operand.
-/

namespace QuantumAlg.Nat.FixedWidth.NearPower

/-- The single subtraction sufficient below twice the modulus. -/
def reduceOnce (modulus value : Nat) : Nat :=
  if modulus ≤ value then value - modulus else value

lemma reduceOnce_eq_mod {modulus value : Nat} (bounded : value < 2 * modulus) :
    reduceOnce modulus value = value % modulus := by
  by_cases wrapped : modulus ≤ value
  · have small : value - modulus < modulus := by omega
    rw [reduceOnce, if_pos wrapped, Nat.mod_eq_sub_mod wrapped, Nat.mod_eq_of_lt small]
  · rw [reduceOnce, if_neg wrapped, Nat.mod_eq_of_lt (by omega)]

lemma reduceOnce_lt {modulus value : Nat} (positive : 0 < modulus)
    (bounded : value < 2 * modulus) :
    reduceOnce modulus value < modulus := by
  rw [reduceOnce_eq_mod bounded]
  exact Nat.mod_lt _ positive

/-- A modular-addition wrap can be erased by comparing the result with its preserved addend. -/
lemma add_wrap_iff_result_lt {modulus left right : Nat}
    (rightCanonical : right < modulus) :
    modulus ≤ left + right ↔ reduceOnce modulus (left + right) < left := by
  by_cases wrapped : modulus ≤ left + right
  · rw [reduceOnce, if_pos wrapped]
    omega
  · rw [reduceOnce, if_neg wrapped]
    omega

/-- The carry bit of an addition and its low-word comparison select the same single reduction. -/
lemma full_carry_wrap_iff {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) :
    (capacity ≤ value ∨ modulus ≤ value % capacity) ↔ modulus ≤ value := by
  by_cases carry : capacity ≤ value
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The low word after the conditional complement correction. -/
def correctedLow (modulus complement capacity value : Nat) : Nat :=
  if capacity ≤ value ∨ modulus ≤ value % capacity then
    (value % capacity + complement) % capacity
  else value % capacity

lemma correctedLow_eq_reduceOnce {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (bounded : value < 2 * modulus) :
    correctedLow modulus complement capacity value = reduceOnce modulus value := by
  have belowTwiceCapacity : value < 2 * capacity := by omega
  by_cases carry : capacity ≤ value
  · have low : value % capacity = value - capacity := by
      rw [Nat.mod_eq_sub_mod carry, Nat.mod_eq_of_lt (by omega)]
    have corrected : value - capacity + complement = value - modulus := by omega
    have wrapped : modulus ≤ value := by omega
    have canonical : value - modulus < capacity := by omega
    rw [correctedLow, if_pos (Or.inl carry), low, corrected,
      Nat.mod_eq_of_lt canonical, reduceOnce, if_pos wrapped]
  · have low : value % capacity = value := Nat.mod_eq_of_lt (by omega)
    by_cases wrapped : modulus ≤ value
    · have corrected : value + complement - capacity = value - modulus := by omega
      have overflow : capacity ≤ value + complement := by omega
      rw [correctedLow, if_pos (Or.inr (by simpa only [low] using wrapped)), low,
        Nat.mod_eq_sub_mod overflow, corrected, Nat.mod_eq_of_lt (by omega),
        reduceOnce, if_pos wrapped]
    · rw [correctedLow, if_neg (by simpa only [low] using not_or_intro carry wrapped),
        low, reduceOnce, if_neg wrapped]

lemma correctedLow_eq_mod {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity)
    (bounded : value < 2 * modulus) :
    correctedLow modulus complement capacity value = value % modulus := by
  rw [correctedLow_eq_reduceOnce capacity_eq bounded, reduceOnce_eq_mod bounded]

/-- Numeric form of a cyclic left shift at a power-of-two capacity. -/
def rotatedWord (capacity value : Nat) : Nat :=
  (2 * value) % capacity + if capacity ≤ 2 * value then 1 else 0

/-- The first high-bit-selected complement correction, before the final single subtraction. -/
def doubleIntermediate (modulus capacity value : Nat) : Nat :=
  if capacity ≤ 2 * value then 2 * value - modulus else 2 * value

lemma rotatedWord_add_even_correction {modulus complement capacity value : Nat}
    (complementPositive : 0 < complement) (capacity_eq : modulus + complement = capacity)
    (canonical : value < modulus) :
    rotatedWord capacity value +
        (if capacity ≤ 2 * value then complement - 1 else 0) =
      doubleIntermediate modulus capacity value := by
  by_cases carry : capacity ≤ 2 * value
  · have low : (2 * value) % capacity = 2 * value - capacity := by
      rw [Nat.mod_eq_sub_mod carry, Nat.mod_eq_of_lt (by omega)]
    simp only [rotatedWord, doubleIntermediate, if_pos carry, low]
    omega
  · have low : (2 * value) % capacity = 2 * value := Nat.mod_eq_of_lt (by omega)
    simp only [rotatedWord, doubleIntermediate, if_neg carry, low]
    omega

lemma doubleIntermediate_lt_twice {modulus capacity value : Nat}
    (canonical : value < modulus) :
    doubleIntermediate modulus capacity value < 2 * modulus := by
  unfold doubleIntermediate
  split_ifs <;> omega

lemma double_reduceOnce_eq_mod {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity)
    (canonical : value < modulus) :
    reduceOnce modulus (doubleIntermediate modulus capacity value) =
      (2 * value) % modulus := by
  by_cases carry : capacity ≤ 2 * value
  · have wrapped : modulus ≤ 2 * value := by omega
    have small : 2 * value - modulus < modulus := by omega
    rw [doubleIntermediate, if_pos carry, reduceOnce, if_neg (by omega),
      Nat.mod_eq_sub_mod wrapped, Nat.mod_eq_of_lt small]
  · rw [doubleIntermediate, if_neg carry]
    exact reduceOnce_eq_mod (by omega)

/-- The second correction flag is recoverable from the final parity and a small comparison. -/
lemma double_cleanup_iff {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (oddModulus : modulus % 2 = 1)
    (canonical : value < modulus) :
    modulus ≤ doubleIntermediate modulus capacity value ↔
      reduceOnce modulus (doubleIntermediate modulus capacity value) % 2 = 1 ∧
        reduceOnce modulus (doubleIntermediate modulus capacity value) < complement := by
  by_cases carry : capacity ≤ 2 * value
  · have small : 2 * value - modulus < modulus := by omega
    rw [doubleIntermediate, if_pos carry, reduceOnce, if_neg (by omega)]
    omega
  · rw [doubleIntermediate, if_neg carry]
    by_cases wrapped : modulus ≤ 2 * value
    · rw [reduceOnce, if_pos wrapped]
      omega
    · rw [reduceOnce, if_neg wrapped]
      omega

/-- On an odd result, comparison with an odd constant reads only the upper bits. -/
lemma odd_comparison_upper_bits {constant value : Nat}
    (oddConstant : constant % 2 = 1) (oddValue : value % 2 = 1) :
    value < constant ↔ value / 2 < constant / 2 := by
  omega

end QuantumAlg.Nat.FixedWidth.NearPower
