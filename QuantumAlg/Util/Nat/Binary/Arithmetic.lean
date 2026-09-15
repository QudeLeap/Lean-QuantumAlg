/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.BinaryRec

/-!
# Binary natural-number arithmetic

This module contains circuit-independent arithmetic facts about binary natural
numbers.  Quantum register layouts and gate schedules consume these facts, but
the statements and proofs do not depend on quantum data types.
-/

section

namespace QuantumAlg
namespace Nat.BinaryArithmetic

/-- Boolean carry sequence for natural-number addition, ordered from least
significant to most significant bit. -/
def natAddCarry (a b : Nat) : Nat -> Bool
  | 0 => false
  | i + 1 => Bool.carry (a.testBit i) (b.testBit i) (natAddCarry a b i)

theorem bool_carry_comm (a b c : Bool) :
    Bool.carry a b c = Bool.carry b a c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem natAddCarry_comm (a b i : Nat) :
    natAddCarry a b i = natAddCarry b a i := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      simp [natAddCarry, ih, bool_carry_comm]

/-- One-step numeric identity for adding two `Nat.bit` decompositions plus an
incoming carry bit. -/
theorem bit_add_bit (a b c : Bool) (ah bh : Nat) :
    Nat.bit a ah + Nat.bit b bh + c.toNat =
      Nat.bit ((a ^^ b) ^^ c) (ah + bh + (Bool.carry a b c).toNat) := by
  cases a <;> cases b <;> cases c <;>
    simp [Nat.bit, Bool.carry] <;> omega

/-- Shifting away the first `i` bits of `a + b` leaves the shifted addends plus
the carry propagated through the low `i` bits. -/
theorem shifted_add_decomp (a b i : Nat) :
    (a + b) >>> i = (a >>> i) + (b >>> i) + (natAddCarry a b i).toNat := by
  induction i with
  | zero =>
      simp [natAddCarry]
  | succ i ih =>
      rw [show i + 1 = i + 1 by rfl]
      rw [Nat.shiftRight_add]
      rw [ih]
      have hbit := bit_add_bit ((a >>> i).testBit 0) ((b >>> i).testBit 0)
        (natAddCarry a b i) ((a >>> i) >>> 1) ((b >>> i) >>> 1)
      have ha :
          Nat.bit ((a >>> i).testBit 0) ((a >>> i) >>> 1) = a >>> i :=
        Nat.bit_testBit_zero_shiftRight_one (a >>> i)
      have hb :
          Nat.bit ((b >>> i).testBit 0) ((b >>> i) >>> 1) = b >>> i :=
        Nat.bit_testBit_zero_shiftRight_one (b >>> i)
      rw [ha, hb] at hbit
      rw [hbit]
      rw [Nat.bit_shiftRight_one]
      simp [natAddCarry, Nat.shiftRight_add, Nat.add_assoc]

/-- For two `n`-bit naturals, the propagated carry out of bit `n-1` is
exactly the overflow predicate for their sum. -/
theorem natAddCarry_eq_decide_two_pow_le {a b n : Nat}
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    natAddCarry a b n = decide (2 ^ n ≤ a + b) := by
  have haShift : a >>> n = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt ha
  have hbShift : b >>> n = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hb
  have hshift : (a + b) >>> n = (natAddCarry a b n).toNat := by
    rw [shifted_add_decomp, haShift, hbShift]
    simp
  rw [Nat.shiftRight_eq_div_pow] at hshift
  cases hcarry : natAddCarry a b n <;>
    simp only [hcarry, Bool.toNat_false, Bool.toNat_true] at hshift ⊢
  · apply Eq.symm
    exact decide_eq_false (by
      intro hle
      have hpos : 0 < (a + b) / 2 ^ n :=
        Nat.div_pos hle (Nat.two_pow_pos n)
      exact (Nat.ne_of_gt hpos) hshift)
  · apply Eq.symm
    exact decide_eq_true (by
      by_contra hnot
      have hlt : a + b < 2 ^ n := Nat.lt_of_not_ge hnot
      have hzero : (a + b) / 2 ^ n = 0 := Nat.div_eq_of_lt hlt
      rw [hzero] at hshift
      contradiction)

/-- Low-bit addition formula with an explicit incoming carry bit. -/
theorem testBit_zero_add_with_carry (a b : Nat) (c : Bool) :
    (a + b + c.toNat).testBit 0 = ((a.testBit 0 ^^ b.testBit 0) ^^ c) := by
  have ha : Nat.bit (a.testBit 0) (a >>> 1) = a :=
    Nat.bit_testBit_zero_shiftRight_one a
  have hb : Nat.bit (b.testBit 0) (b >>> 1) = b :=
    Nat.bit_testBit_zero_shiftRight_one b
  rw [ha.symm, hb.symm]
  rw [bit_add_bit (a.testBit 0) (b.testBit 0) c (a >>> 1) (b >>> 1)]
  cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0 <;> cases c <;>
    simp

/-- Each bit of `a + b` is the xor of the two input bits and the propagated
incoming carry at that bit. -/
theorem testBit_add_eq_xor3 (a b i : Nat) :
    (a + b).testBit i = ((a.testBit i ^^ b.testBit i) ^^ natAddCarry a b i) := by
  rw [show (a + b).testBit i = ((a + b) >>> i).testBit 0 by
    rw [Nat.testBit_shiftRight]
    rfl]
  rw [shifted_add_decomp a b i]
  rw [testBit_zero_add_with_carry]
  simp

/-- A natural below `2^(n+1)` whose bit `n` is clear is below `2^n`. -/
theorem lt_two_pow_of_lt_two_pow_succ_testBit_false
    {x n : Nat} (hlt : x < 2 ^ (n + 1))
    (hbit : x.testBit n = false) :
    x < 2 ^ n := by
  have hdecomp :
      x % 2 ^ (n + 1) =
        x % 2 ^ n + (x.testBit n).toNat * 2 ^ n := by
    rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]
  have hmod : x % 2 ^ (n + 1) = x := Nat.mod_eq_of_lt hlt
  have hx : x = x % 2 ^ n := by
    calc
      x = x % 2 ^ (n + 1) := hmod.symm
      _ = x % 2 ^ n + (x.testBit n).toNat * 2 ^ n := hdecomp
      _ = x % 2 ^ n := by simp [hbit]
  rw [hx]
  exact Nat.mod_lt x (Nat.two_pow_pos n)

/-- Increment toggles the least-significant bit. -/
theorem testBit_zero_add_one (a : Nat) :
    (a + 1).testBit 0 = !a.testBit 0 := by
  have h := testBit_add_eq_xor3 a 1 0
  simpa [natAddCarry] using h

/-- Increment toggles bit one exactly when bit zero is set. -/
theorem testBit_one_add_one (a : Nat) :
    (a + 1).testBit 1 = (a.testBit 1 ^^ a.testBit 0) := by
  have h := testBit_add_eq_xor3 a 1 1
  have honeZero : Nat.testBit 1 0 = true := by decide
  have honeOne : Nat.testBit 1 1 = false := by decide
  rw [honeOne] at h
  cases hzero : a.testBit 0
  all_goals
    simpa [natAddCarry, Bool.carry, hzero, honeZero] using h

/-- Increment toggles bit two exactly when both lower bits are set. -/
theorem testBit_two_add_one (a : Nat) :
    (a + 1).testBit 2 =
      (a.testBit 2 ^^ (a.testBit 0 && a.testBit 1)) := by
  have h := testBit_add_eq_xor3 a 1 2
  have honeZero : Nat.testBit 1 0 = true := by decide
  have honeOne : Nat.testBit 1 1 = false := by decide
  have honeTwo : Nat.testBit 1 2 = false := by decide
  rw [honeTwo] at h
  cases hzero : a.testBit 0 <;> cases hone : a.testBit 1
  all_goals
    simpa [natAddCarry, Bool.carry, hzero, hone, honeZero, honeOne] using h

/-- Doubling and halving cancel on an even natural. -/
theorem two_mul_div_two_of_mod_two_eq_zero
    (x : Nat) (h : x % 2 = 0) :
    2 * (x / 2) = x := by
  have hdvd : 2 ∣ x := Nat.dvd_of_mod_eq_zero h
  simpa [Nat.mul_comm] using Nat.div_mul_cancel hdvd

/-- The difference of two odd naturals is even when the subtraction is
nontruncated. -/
theorem sub_mod_two_eq_zero_of_mod_two_ne_zero
    {a b : Nat} (hle : b ≤ a) (ha : a % 2 ≠ 0) (hb : b % 2 ≠ 0) :
    (a - b) % 2 = 0 := by
  omega

/-- A set low bit implies an odd natural. -/
theorem mod_two_ne_zero_of_testBit_zero_true
    (x : Nat) (h : x.testBit 0 = true) :
    x % 2 ≠ 0 := by
  have hone : x % 2 = 1 := by
    simpa [Nat.testBit_zero] using h
  omega

/-- A cleared low bit implies an even natural. -/
theorem mod_two_eq_zero_of_testBit_zero_false
    (x : Nat) (h : x.testBit 0 = false) :
    x % 2 = 0 := by
  have hlt : x % 2 < 2 := Nat.mod_lt _ (by decide)
  have hcases : x % 2 = 0 ∨ x % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · exact hzero
  · have htrue : x.testBit 0 = true := by
      simpa [Nat.testBit_zero] using hone
    rw [h] at htrue
    contradiction

/-- A set low bit implies a nonzero natural. -/
theorem ne_zero_of_testBit_zero_true
    (x : Nat) (h : x.testBit 0 = true) :
    x ≠ 0 := by
  intro hzero
  have hmod : x % 2 = 0 := by simp [hzero]
  exact mod_two_ne_zero_of_testBit_zero_true x h hmod

end Nat.BinaryArithmetic
end QuantumAlg

end
