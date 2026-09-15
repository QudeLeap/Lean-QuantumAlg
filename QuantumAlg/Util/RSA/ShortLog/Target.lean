/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Original centered target arithmetic for short-log recovery

The literal arithmetic choice handles zero first, then negative values below
half the source modulus, and the nonnegative complement otherwise. Its value
is the existing centered modular negation of the scaled source k coordinate.
The half-modulus tie retains the original nonnegative representative. Both
source widths and wide native implementations use this one mathematical owner.
-/

namespace QuantumAlg.RSA.ShortLogTarget

/-- The intended centered representative of one modular coordinate. -/
def centeredValue (a modulus : Nat) : Int :=
  if a = 0 then
    0
  else if a < modulus / 2 then
    -(a : Int)
  else
    (modulus : Int) - a

/-- The centered raw routine agrees with the pure short-log target coordinate. -/
theorem centeredValue_eq_shortLogTargetCoordinate (m ell : Nat)
    (sample : RSA.ShortLogSample m ell) :
    centeredValue (2 ^ m * sample.2.val) (2 ^ (ell + m)) =
      RSA.shortLogTargetCoordinate m ell sample := by
  let value := 2 ^ m * sample.2.val
  let modulus := 2 ^ (ell + m)
  have valueLt : value < modulus := by
    dsimp only [value, modulus]
    calc
      2 ^ m * sample.2.val < 2 ^ m * 2 ^ ell :=
        Nat.mul_lt_mul_of_pos_left sample.2.isLt (pow_pos (by norm_num) _)
      _ = 2 ^ (m + ell) := (pow_add 2 m ell).symm
      _ = 2 ^ (ell + m) := by rw [Nat.add_comm m ell]
  change centeredValue value modulus =
    NumberTheory.centeredResidue modulus (NumberTheory.modularNegation modulus value)
  by_cases valueZero : value = 0
  · simp [centeredValue, NumberTheory.centeredResidue,
      NumberTheory.modularNegation, valueZero]
  have valuePos : 0 < value := Nat.pos_of_ne_zero valueZero
  have negationEq : NumberTheory.modularNegation modulus value = modulus - value := by
    unfold NumberTheory.modularNegation
    rw [Nat.mod_eq_of_lt valueLt]
    exact Nat.mod_eq_of_lt (by omega)
  have complementLt : modulus - value < modulus := by omega
  rw [negationEq]
  simp only [NumberTheory.centeredResidue, Nat.mod_eq_of_lt complementLt]
  unfold centeredValue
  rw [if_neg valueZero]
  cases sumEq : ell + m with
  | zero =>
      have modulusOne : modulus = 1 := by simp [modulus, sumEq]
      omega
  | succ e =>
      have modulusEq : modulus = 2 * 2 ^ e := by
        simp [modulus, sumEq, pow_succ, mul_comm]
      have halfEq : modulus / 2 = 2 ^ e := by
        rw [modulusEq]
        omega
      by_cases belowHalf : value < modulus / 2
      · have upperHalf : ¬ 2 * (modulus - value) ≤ modulus := by
          rw [halfEq] at belowHalf
          rw [modulusEq]
          omega
        rw [if_pos belowHalf, if_neg upperHalf]
        rw [Nat.cast_sub (Nat.le_of_lt valueLt)]
        omega
      · have lowerHalf : 2 * (modulus - value) ≤ modulus := by
          rw [halfEq] at belowHalf
          rw [modulusEq]
          omega
        rw [if_neg belowHalf, if_pos lowerHalf]
        exact (Nat.cast_sub (Nat.le_of_lt valueLt)).symm

end QuantumAlg.RSA.ShortLogTarget
