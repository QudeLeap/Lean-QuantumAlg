/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower
import Mathlib.Logic.Equiv.Defs

/-!
# Doubling and its exact inverse on every residue of an odd modulus

The operand can be zero. Oddness belongs to the fixed modulus, rather than
to a runtime field operand. These finite arithmetic laws justify reversing
an independently realized doubling program without restricting its input.
-/

namespace QuantumAlg.Nat.FixedWidth.OddDoubling

/-- Canonical multiplication by two; the positive modulus follows from the input type. -/
def double {modulus : Nat} (value : Fin modulus) : Fin modulus :=
  ⟨(2 * value.val) % modulus, Nat.mod_lt _ (by have := value.isLt; omega)⟩

/-- A canonical even residue halves directly; an odd residue first adds the odd modulus. -/
def half {modulus : Nat} (value : Fin modulus) : Fin modulus :=
  ⟨if value.val % 2 = 0 then value.val / 2 else (value.val + modulus) / 2, by
    have bounded := value.isLt
    split_ifs <;> omega⟩

lemma half_double {modulus : Nat} (odd : modulus % 2 = 1) (value : Fin modulus) :
    half (double value) = value := by
  apply Fin.ext
  change (if (2 * value.val % modulus) % 2 = 0 then
    (2 * value.val % modulus) / 2 else (2 * value.val % modulus + modulus) / 2) = value.val
  have bounded := value.isLt
  have reduced : 2 * value.val % modulus = NearPower.reduceOnce modulus (2 * value.val) :=
    (NearPower.reduceOnce_eq_mod (by omega)).symm
  by_cases wrapped : modulus ≤ 2 * value.val
  · simp only [reduced, NearPower.reduceOnce, if_pos wrapped]
    rw [if_neg (by omega)]
    omega
  · simp only [reduced, NearPower.reduceOnce, if_neg wrapped]
    rw [if_pos (by omega)]
    omega

lemma double_half {modulus : Nat} (odd : modulus % 2 = 1) (value : Fin modulus) :
    double (half value) = value := by
  apply Fin.ext
  change 2 * (if value.val % 2 = 0 then value.val / 2 else
    (value.val + modulus) / 2) % modulus = value.val
  have bounded := value.isLt
  by_cases evenValue : value.val % 2 = 0
  · rw [if_pos evenValue, show 2 * (value.val / 2) = value.val by omega,
      Nat.mod_eq_of_lt bounded]
  · have numerator : 2 * ((value.val + modulus) / 2) = value.val + modulus := by omega
    rw [if_neg evenValue, numerator, Nat.add_mod_right, Nat.mod_eq_of_lt bounded]

/-- A mathematical inverse for the actual doubling circuit's canonical endpoint. -/
def doubleEquiv (modulus : Nat) (odd : modulus % 2 = 1) : Equiv.Perm (Fin modulus) where
  toFun := double
  invFun := half
  left_inv := half_double odd
  right_inv := double_half odd

end QuantumAlg.Nat.FixedWidth.OddDoubling
