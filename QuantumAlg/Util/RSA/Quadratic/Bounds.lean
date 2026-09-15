/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Reduction
import Mathlib.Data.Nat.Sqrt
import Lean.Elab.Tactic.Omega

/-!
# Exact word capacities for the source quadratic recovery

A logarithm represented by a width-word has center at most `2 ^ width`.
The work width `(width + 1) + (width + 1)` consequently holds its full square,
truncated discriminant, square root and both candidate factors. These are
arithmetic bounds for the original source expressions, including logarithm
zero and a zero-width logarithm word. No modulus parity or RSA-key premise
is used to justify the actual finite arithmetic.
-/

namespace QuantumAlg.RSA

/-- Actual word capacity sufficient for the entire quadratic candidate computation. -/
def quadraticWordWidth (width : Nat) : Nat := (width + 1) + (width + 1)

/-- Adding the source's one to a represented logarithm cannot exceed the next binary endpoint. -/
theorem quadraticCenter_le_wordEndpoint {width logarithm : Nat}
    (represented : logarithm < 2 ^ width) : quadraticCenter logarithm ≤ 2 ^ width := by
  unfold quadraticCenter
  omega

/-- The widened center is exact at every logarithm width. -/
theorem quadraticCenter_lt_wordCapacity {width logarithm : Nat}
    (represented : logarithm < 2 ^ width) :
    quadraticCenter logarithm < 2 ^ quadraticWordWidth width :=
  (quadraticCenter_le_wordEndpoint represented).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by unfold quadraticWordWidth; omega))

/-- The full center square fits the actual work word without discarding any high bit. -/
theorem quadraticSquare_lt_wordCapacity {width logarithm : Nat}
    (represented : logarithm < 2 ^ width) :
    quadraticCenter logarithm ^ 2 < 2 ^ quadraticWordWidth width := by
  have bounded : quadraticCenter logarithm ^ 2 ≤ 2 ^ (width + width) := by
    calc
      _ ≤ (2 ^ width) ^ 2 := Nat.pow_le_pow_left (quadraticCenter_le_wordEndpoint represented) 2
      _ = 2 ^ (width + width) := by rw [pow_two, Nat.pow_add]
  exact bounded.trans_lt
    (Nat.pow_lt_pow_right (by decide) (by unfold quadraticWordWidth; omega))

/-- Source truncation on a negative discriminant still fits the same real work word. -/
theorem quadraticDiscriminant_lt_wordCapacity {width logarithm : Nat} (modulus : Nat)
    (represented : logarithm < 2 ^ width) :
    quadraticDiscriminant modulus logarithm < 2 ^ quadraticWordWidth width :=
  (Nat.sub_le _ _).trans_lt (quadraticSquare_lt_wordCapacity represented)

/-- The source square root never exceeds the center, including a discriminant truncated to zero. -/
theorem quadraticRoot_le_center (modulus logarithm : Nat) :
    Nat.sqrt (quadraticDiscriminant modulus logarithm) ≤ quadraticCenter logarithm := by
  have monotone := Nat.sqrt_le_sqrt (Nat.sub_le (quadraticCenter logarithm ^ 2) modulus)
  simpa only [Nat.sqrt_eq', quadraticDiscriminant] using monotone

/-- The source's lower candidate fits the same actual work capacity. -/
theorem quadraticFirst_lt_wordCapacity {width logarithm : Nat} (modulus : Nat)
    (represented : logarithm < 2 ^ width) :
    quadraticCenter logarithm - Nat.sqrt (quadraticDiscriminant modulus logarithm) <
      2 ^ quadraticWordWidth width :=
  (Nat.sub_le _ _).trans_lt (quadraticCenter_lt_wordCapacity represented)

/-- The source's upper candidate also fits, including the largest represented logarithm. -/
theorem quadraticSecond_lt_wordCapacity {width logarithm : Nat} (modulus : Nat)
    (represented : logarithm < 2 ^ width) :
    quadraticCenter logarithm + Nat.sqrt (quadraticDiscriminant modulus logarithm) <
      2 ^ quadraticWordWidth width := by
  have center := quadraticCenter_le_wordEndpoint represented
  have root := (quadraticRoot_le_center modulus logarithm).trans center
  have bounded : quadraticCenter logarithm + Nat.sqrt (quadraticDiscriminant modulus logarithm) ≤
      2 ^ (width + 1) := by
    calc
      _ ≤ 2 ^ width + 2 ^ width := Nat.add_le_add center root
      _ = 2 ^ (width + 1) := by rw [Nat.pow_succ, Nat.mul_two]
  exact bounded.trans_lt
    (Nat.pow_lt_pow_right (by decide) (by unfold quadraticWordWidth; omega))

end QuantumAlg.RSA
