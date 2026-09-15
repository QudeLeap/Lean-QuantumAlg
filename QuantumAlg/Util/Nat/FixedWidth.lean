/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Nat.Binary.Arithmetic
import Mathlib.Tactic

/-!
# Fixed-width binary words

This quantum-free module owns the mathematical definitions used by the
fixed-round binary-GCD realization.  Physical registers and gate schedules
remain in `QuantumAlg.Primitives`.
-/

section

namespace QuantumAlg
namespace Nat.FixedWidth

/-- A raw `width`-bit word label.  The concrete compute circuit will replace
word-level updates by addressed X/CNOT/Toffoli networks over these finite basis
labels. -/
public abbrev Word (width : Nat) := Fin (2 ^ width)


/-- Width-preserving natural halving of a finite word. -/
def wordHalf (width : Nat) (x : Word width) : Word width :=
  ⟨x.val / 2, lt_of_le_of_lt (Nat.div_le_self x.val 2) x.isLt⟩

@[simp] theorem wordHalf_val (width : Nat) (x : Word width) :
    (wordHalf width x).val = x.val / 2 :=
  rfl

/-- Width-preserving natural doubling of a finite word. -/
def wordDouble (width : Nat) (x : Word width) : Word width :=
  ⟨(x.val <<< 1) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩

@[simp] theorem wordDouble_val (width : Nat) (x : Word width) :
    (wordDouble width x).val = (x.val <<< 1) % 2 ^ width :=
  rfl

/-- Width-preserving natural increment of a finite word. -/
def wordIncrement (width : Nat) (x : Word width) : Word width :=
  ⟨(x.val + 1) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩

@[simp] theorem wordIncrement_val (width : Nat) (x : Word width) :
    (wordIncrement width x).val = (x.val + 1) % 2 ^ width :=
  rfl

/-- Adding the finite word `1` is the width-preserving increment helper. -/
theorem word_add_one_eq_wordIncrement (width : Nat) (x : Word width) :
    x + (1 : Word width) = wordIncrement width x := by
  apply Fin.ext
  simp [wordIncrement, Fin.val_add]

theorem wordDouble_val_of_no_overflow
    (width : Nat) (x : Word width) (h : 2 * x.val < 2 ^ width) :
    (wordDouble width x).val = 2 * x.val := by
  rw [wordDouble_val, Nat.shiftLeft_eq]
  have hmul : x.val * 2 ^ 1 = 2 * x.val := by
    simp [Nat.mul_comm]
  rw [hmul]
  exact Nat.mod_eq_of_lt h

theorem word_two_mul_lt_of_msb_false
    {width : Nat} (x : Word (width + 1))
    (hmsb : x.val.testBit (Fin.last width).val = false) :
    2 * x.val < 2 ^ (width + 1) := by
  have hxlt : x.val < 2 ^ width :=
    Nat.BinaryArithmetic.lt_two_pow_of_lt_two_pow_succ_testBit_false x.isLt
      (by simpa [Fin.last] using hmsb)
  have hdouble : 2 * x.val < 2 * 2 ^ width := by
    nlinarith [Nat.two_pow_pos width]
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdouble

theorem word_add_val_lt_two_pow_succ_of_msb_false
    {width : Nat} (left right : Word (width + 1))
    (hleft : left.val.testBit (Fin.last width).val = false)
    (hright : right.val.testBit (Fin.last width).val = false) :
    left.val + right.val < 2 ^ (width + 1) := by
  have hleftLt : left.val < 2 ^ width :=
    Nat.BinaryArithmetic.lt_two_pow_of_lt_two_pow_succ_testBit_false left.isLt
      (by simpa [Fin.last] using hleft)
  have hrightLt : right.val < 2 ^ width :=
    Nat.BinaryArithmetic.lt_two_pow_of_lt_two_pow_succ_testBit_false right.isLt
      (by simpa [Fin.last] using hright)
  have hadd : left.val + right.val < 2 * 2 ^ width := by
    nlinarith [Nat.two_pow_pos width]
  simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hadd


/-- The low bit of a nonempty width-preserving increment is the toggled
original low bit. -/
theorem wordIncrement_testBit_zero {tail : Nat} (x : Word tail.succ) :
    (wordIncrement tail.succ x).val.testBit 0 = !x.val.testBit 0 := by
  rw [wordIncrement_val, Nat.testBit_mod_two_pow]
  simp
  simpa [Nat.testBit_zero] using Nat.BinaryArithmetic.testBit_zero_add_one x.val


/-- The second-lowest bit of a width-preserving increment is toggled exactly by
the original low bit. -/
theorem wordIncrement_testBit_one {tail : Nat} (x : Word tail.succ.succ) :
    (wordIncrement tail.succ.succ x).val.testBit 1 =
      (x.val.testBit 1 ^^ x.val.testBit 0) := by
  rw [wordIncrement_val, Nat.testBit_mod_two_pow]
  simp
  simpa using Nat.BinaryArithmetic.testBit_one_add_one x.val


/-- The third-lowest bit of a width-preserving increment is toggled exactly by
the original two lower bits. -/
theorem wordIncrement_testBit_two {tail : Nat} (x : Word tail.succ.succ.succ) :
    (wordIncrement tail.succ.succ.succ x).val.testBit 2 =
      (x.val.testBit 2 ^^ (x.val.testBit 0 && x.val.testBit 1)) := by
  rw [wordIncrement_val, Nat.testBit_mod_two_pow]
  simp
  simpa using Nat.BinaryArithmetic.testBit_two_add_one x.val

/-- Low-bit readout for the width-preserving natural halving helper. -/
theorem wordHalf_testBit (width : Nat) (x : Word width) (bit : Fin width) :
    (wordHalf width x).val.testBit bit.val =
      x.val.testBit (bit.val + 1) := by
  simp [wordHalf, Nat.testBit_div_two]

/-- Low-bit readout for the width-preserving natural doubling helper. -/
theorem wordDouble_testBit (width : Nat) (x : Word width) (bit : Fin width) :
    (wordDouble width x).val.testBit bit.val =
      (decide (bit.val ≥ 1) && x.val.testBit (bit.val - 1)) := by
  unfold wordDouble
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_shiftLeft]
  simp [bit.isLt]

/-- Finite words are equal when all in-range value bits agree. -/
theorem word_eq_of_testBit_eq {width : Nat} {a b : Word width}
    (h : forall bit : Fin width,
      a.val.testBit bit.val = b.val.testBit bit.val) :
    a = b := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < width
  · exact h ⟨bit, hbit⟩
  · have hwidth : width <= bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ width <= 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hwidth
    have ha : a.val.testBit bit = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hpow)
    have hb : b.val.testBit bit = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hpow)
    rw [ha, hb]

theorem word_sub_testBit_zero_false_of_odd_lt
    {width : Nat} (u v : Word width)
    (huOdd : u.val.testBit (0 : Nat) = true)
    (hvOdd : v.val.testBit (0 : Nat) = true) (hlt : v.val < u.val) :
    (u - v).val.testBit (0 : Nat) = false := by
  have hsubVal : (u - v).val = u.val - v.val := by
    exact Fin.sub_val_of_le (Nat.le_of_lt hlt)
  have huMod : u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true u.val huOdd
  have hvMod : v.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true v.val hvOdd
  have hmod : (u.val - v.val) % 2 = 0 :=
    Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero (Nat.le_of_lt hlt) huMod hvMod
  rw [hsubVal]
  simp [Nat.testBit_zero, hmod]

theorem word_sub_testBit_zero_false_of_odd_not_lt
    {width : Nat} (u v : Word width)
    (huOdd : u.val.testBit (0 : Nat) = true)
    (hvOdd : v.val.testBit (0 : Nat) = true) (hnlt : ¬ v.val < u.val) :
    (v - u).val.testBit (0 : Nat) = false := by
  have hle : u.val <= v.val := Nat.le_of_not_gt hnlt
  have hsubVal : (v - u).val = v.val - u.val := by
    exact Fin.sub_val_of_le hle
  have huMod : u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true u.val huOdd
  have hvMod : v.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true v.val hvOdd
  have hmod : (v.val - u.val) % 2 = 0 :=
    Nat.BinaryArithmetic.sub_mod_two_eq_zero_of_mod_two_ne_zero hle hvMod huMod
  rw [hsubVal]
  simp [Nat.testBit_zero, hmod]

end Nat.FixedWidth
end QuantumAlg

end
