/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Nat.Binary.Arithmetic
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Natural-number utility lemmas

This module collects quantum-free natural-number helpers used across resource
formulas. These definitions are purely arithmetic adapters, not algorithm
claims.
-/

section

namespace QuantumAlg
namespace Nat

/-- Integer ceiling of a nonnegative rational coefficient `num / den`, encoded
as the standard natural-number upper-bound expression. -/
def ceilDiv (num den : ℕ) : ℕ :=
  (num + den - 1) / den

@[simp]
lemma ceilDiv_eq (num den : ℕ) :
    ceilDiv num den = (num + den - 1) / den :=
  rfl

/-- Multiplying a ceiling quotient by its positive denominator recovers at
least the numerator. -/
lemma le_ceilDiv_mul {num den : ℕ} (hden : 0 < den) :
    num ≤ ceilDiv num den * den := by
  have hmod := Nat.mod_lt (num + den - 1) hden
  have hdecomp := Nat.div_add_mod (num + den - 1) den
  have hcomm :
      den * ((num + den - 1) / den) =
        ((num + den - 1) / den) * den := Nat.mul_comm _ _
  unfold ceilDiv
  omega

/-- The overshoot produced by a natural-number ceiling quotient is strictly
less than one positive denominator. -/
lemma ceilDiv_mul_lt_add {num den : ℕ} (hden : 0 < den) :
    ceilDiv num den * den < num + den := by
  have hle := Nat.div_mul_le_self (num + den - 1) den
  rw [ceilDiv]
  omega

end Nat
end QuantumAlg

end
