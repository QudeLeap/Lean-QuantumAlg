/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Domain

/-!
# Original prime order throughout every small-base doubling

Every successive doubling retains the original odd prime point order.
The argument iterates the two-times rule rather than assuming the large
scalar two-to-256 remains below that order. No scalar address is truncated.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

noncomputable section

/-- Doubling preserves the exact original prime order on the original order-above-three domain. -/
lemma double_addOrderOf {G : Type*} [AddGroup G] (point : G) (order : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order) :
    addOrderOf (point + point) = order := by
  simpa only [two_nsmul] using prime_order_nsmul point order 2 prime original (by omega) (by omega)

/-- Every actual successive power-of-two base retains the same original prime point order. -/
lemma pow_two_nsmul_addOrderOf {G : Type*} [AddGroup G] (point : G) (order count : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order) :
    addOrderOf ((2 ^ count) • point) = order := by
  induction count with
  | zero => simpa only [pow_zero, one_nsmul] using original
  | succ count ih =>
      rw [pow_succ, Nat.mul_two, add_nsmul]
      exact double_addOrderOf _ order prime large ih

/-- None of those original bases has a zero doubled point. -/
lemma pow_two_nsmul_double_ne_zero {G : Type*} [AddGroup G] (point : G) (order count : Nat)
    (prime : order.Prime) (large : 3 < order) (original : addOrderOf point = order) :
    (2 ^ count) • point + (2 ^ count) • point ≠ 0 := by
  have current := pow_two_nsmul_addOrderOf point order count prime large original
  have nonzero : (2 : Nat) • ((2 ^ count) • point) ≠ 0 :=
    nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [current]; omega)
  simpa only [two_nsmul] using nonzero

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
