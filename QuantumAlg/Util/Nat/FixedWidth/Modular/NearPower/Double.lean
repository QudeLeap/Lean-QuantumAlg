/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower

/-! # Complete-width bounds for the actual two-correction doubling schedule -/

namespace QuantumAlg.Nat.FixedWidth.NearPower

/-- The first correction fits the original word even when its rotated high bit was set. -/
lemma doubleIntermediate_lt_capacity {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (canonical : value < modulus) :
    doubleIntermediate modulus capacity value < capacity := by
  unfold doubleIntermediate
  split_ifs <;> omega

/-- The native even correction cannot introduce another complete-word wrap. -/
lemma rotatedWord_even_correction_mod {modulus complement capacity value : Nat}
    (positive : 0 < complement) (capacity_eq : modulus + complement = capacity)
    (canonical : value < modulus) :
    (rotatedWord capacity value +
      (if capacity ≤ 2 * value then complement - 1 else 0)) % capacity =
        doubleIntermediate modulus capacity value := by
  rw [rotatedWord_add_even_correction positive capacity_eq canonical]
  exact Nat.mod_eq_of_lt (doubleIntermediate_lt_capacity capacity_eq canonical)

/-- The second actual conditional complement gives the complete canonical doubled value. -/
lemma double_conditional_complement_eq_mod {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (canonical : value < modulus) :
    (if modulus ≤ doubleIntermediate modulus capacity value then
      (doubleIntermediate modulus capacity value + complement) % capacity
    else doubleIntermediate modulus capacity value) = (2 * value) % modulus := by
  have fits := doubleIntermediate_lt_capacity capacity_eq canonical
  have corrected := correctedLow_eq_reduceOnce capacity_eq
    (doubleIntermediate_lt_twice (capacity := capacity) canonical)
  simp only [correctedLow, Nat.mod_eq_of_lt fits,
    Nat.not_le.mpr fits, false_or] at corrected
  exact corrected.trans (double_reduceOnce_eq_mod capacity_eq canonical)

/-- A selected second correction comes from the unrotated even branch. -/
lemma doubleIntermediate_eq_twice_of_wrap {modulus capacity value : Nat}
    (canonical : value < modulus)
    (wrapped : modulus ≤ doubleIntermediate modulus capacity value) :
    doubleIntermediate modulus capacity value = 2 * value := by
  by_cases high : capacity ≤ 2 * value
  · simp only [doubleIntermediate, if_pos high] at wrapped
    omega
  · exact if_neg high

/-- The second correction's actual input has low bit zero whenever its flag is set. -/
lemma doubleIntermediate_even_of_wrap {modulus capacity value : Nat}
    (canonical : value < modulus)
    (wrapped : modulus ≤ doubleIntermediate modulus capacity value) :
    doubleIntermediate modulus capacity value % 2 = 0 := by
  rw [doubleIntermediate_eq_twice_of_wrap canonical wrapped]
  omega

end QuantumAlg.Nat.FixedWidth.NearPower
