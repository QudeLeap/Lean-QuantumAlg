/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower

/-! # XOR carry predicates and cleanup for canonical modular addition -/

namespace QuantumAlg.Nat.FixedWidth.NearPower

/-- A canonical two-input sum cannot have both the binary carry and the low-word carry. -/
lemma full_carry_disjoint {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (bounded : value < 2 * modulus) :
    ¬ (capacity ≤ value ∧ modulus ≤ value % capacity) := by
  rintro ⟨carry, low⟩
  have residual : value % capacity = value - capacity := by
    rw [Nat.mod_eq_sub_mod carry, Nat.mod_eq_of_lt (by omega)]
  rw [residual] at low
  omega

/-- The two actual XOR writes recover the single modular-reduction predicate. -/
lemma full_carry_xor_eq_wrap {modulus complement capacity value : Nat}
    (capacity_eq : modulus + complement = capacity) (bounded : value < 2 * modulus) :
    (decide (capacity ≤ value) ^^ decide (modulus ≤ value % capacity)) =
      decide (modulus ≤ value) := by
  by_cases carry : capacity ≤ value
  · have low : ¬ modulus ≤ value % capacity := by
      intro selected
      exact full_carry_disjoint capacity_eq bounded ⟨carry, selected⟩
    have wrapped : modulus ≤ value := by omega
    rw [decide_eq_true carry, decide_eq_false low, decide_eq_true wrapped]
    rfl
  · rw [decide_eq_false carry, Nat.mod_eq_of_lt (by omega), Bool.false_xor]

/-- The preserved quantum addend clears the actual modular-reduction output bit. -/
lemma add_wrap_xor_cleanup {modulus left right : Nat} (rightCanonical : right < modulus) :
    (decide (modulus ≤ left + right) ^^
      decide (reduceOnce modulus (left + right) < left)) = false := by
  simp only [add_wrap_iff_result_lt rightCanonical, Bool.xor_self]

end QuantumAlg.Nat.FixedWidth.NearPower
