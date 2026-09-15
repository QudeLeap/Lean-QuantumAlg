/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel

/-!
# Noncommutative telescoping identities

Ring identities for differences of powers and first-order conjugation remainders.
-/

@[expose] public section

namespace QuantumAlg

/-- Noncommutative telescoping identity for powers. -/
theorem noncomm_power_diff {S : Type} [Ring S] (A B : S) (r : ℕ) :
    A ^ r - B ^ r =
      ∑ k ∈ Finset.range r, A ^ (r - 1 - k) * (A - B) * B ^ k := by
  induction r with
  | zero =>
      simp
  | succ d hd =>
      rw [Finset.sum_range_succ']
      calc
        A ^ (d + 1) - B ^ (d + 1)
            = (A ^ d - B ^ d) * B + A ^ d * (A - B) := by
          noncomm_ring
        _ = (∑ k ∈ Finset.range d, A ^ (d - 1 - k) * (A - B) * B ^ k) * B +
              A ^ d * (A - B) := by
          rw [hd]
        _ = (∑ k ∈ Finset.range d, A ^ (d - 1 - k) * (A - B) * B ^ (k + 1)) +
              A ^ d * (A - B) := by
          rw [Finset.sum_mul]
          simp [mul_assoc, pow_succ]
        _ = (∑ k ∈ Finset.range d,
                A ^ (d + 1 - 1 - (k + 1)) * (A - B) * B ^ (k + 1)) +
              A ^ (d + 1 - 1 - 0) * (A - B) * B ^ 0 := by
          congr 1
          · apply Finset.sum_congr rfl
            intro k hk
            have hpow : d - 1 - k = d + 1 - 1 - (k + 1) := by
              rw [Nat.add_sub_cancel, Nat.sub_sub]
              congr 1
              omega
            rw [hpow]
          · simp

/-- A noncommutative algebra identity isolating the second-order remainder in
conjugation-type products. -/
theorem noncomm_conj_first_order_remainder_decompose {S : Type} [Ring S]
    (U V A X : S) :
    U * X * V - (X + (A * X - X * A)) =
      (U - 1 - A) * (X * V) + (1 + A) * (X * (V - 1 + A)) -
        A * (X * A) := by
  noncomm_ring

/-- Algebraic identity: `U^{k+1} - V^{k+1} = U*(U^k - V^k) + (U-V)*V^k`. -/
lemma pow_succ_sub_pow_succ_eq {R : Type*} [Ring R] (U V : R) (k : ℕ) :
    U ^ (k + 1) - V ^ (k + 1) = U * (U ^ k - V ^ k) + (U - V) * V ^ k := by
  rw [pow_succ' U k, pow_succ' V k, mul_sub, sub_mul]
  abel

end QuantumAlg
