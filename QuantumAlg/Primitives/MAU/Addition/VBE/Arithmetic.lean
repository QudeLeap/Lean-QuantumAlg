/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BasisMap
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.CleanInterface
import all QuantumAlg.Primitives.MAU.Addition

/-!
# Arithmetic facts for the VBE modular adder

This module isolates the natural-number and power-of-two-word identities used by
the concrete compare/subtract/add-back circuit from its gate-level realization.
The source route is [VBE95, 9511018.tex:294-327].
-/

section

namespace QuantumAlg
namespace MAU.Addition
namespace VBEArithmetic

/-- One conditional subtraction, valid as modular reduction when the input is
strictly below `2 * N`. -/
def reduceOnce (N s : Nat) : Nat :=
  if N ≤ s then s - N else s

theorem reduceOnce_eq_compareSubtractAddBack (N a b : Nat) :
    reduceOnce N (a + b) = compareSubtractAddBack N a b := by
  rfl

/-- A single conditional subtraction returns a canonical residue whenever its
input is strictly below twice the modulus. -/
theorem reduceOnce_lt {N s : Nat} (_hN : 0 < N) (hs : s < 2 * N) :
    reduceOnce N s < N := by
  unfold reduceOnce
  by_cases hreduce : N ≤ s
  · rw [if_pos hreduce]
    omega
  · rw [if_neg hreduce]
    omega

/-- On the two-modulus input range, one conditional subtraction is reduction
modulo `N`. -/
theorem reduceOnce_eq_mod {N s : Nat} (_hN : 0 < N) (hs : s < 2 * N) :
    reduceOnce N s = s % N := by
  unfold reduceOnce
  by_cases hreduce : N ≤ s
  · have hlt : s - N < N := by omega
    rw [if_pos hreduce, Nat.mod_eq_sub_mod hreduce, Nat.mod_eq_of_lt hlt]
  · have hlt : s < N := by omega
    rw [if_neg hreduce, Nat.mod_eq_of_lt hlt]

/-- Exact representative of a subtraction between two canonical natural
representatives in `ZMod M`. -/
theorem zmodVal_natCast_sub_natCast {M x y : Nat} [NeZero M]
    (hx : x < M) (hy : y < M) :
    ((x : ZMod M) - (y : ZMod M)).val =
      if y ≤ x then x - y else M + x - y := by
  by_cases hxy : y ≤ x
  · rw [if_pos hxy]
    have hvals : (y : ZMod M).val ≤ (x : ZMod M).val := by
      simpa [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy] using hxy
    calc
      ((x : ZMod M) - (y : ZMod M)).val =
          (x : ZMod M).val - (y : ZMod M).val := ZMod.val_sub hvals
      _ = x - y := by
        rw [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]
  · rw [if_neg hxy]
    have hsum : y ≤ M + x := by omega
    have hlt : M + x - y < M := by omega
    have heq :
        (x : ZMod M) - (y : ZMod M) =
          (M + x - y : Nat) := by
      rw [Nat.cast_sub hsum, Nat.cast_add, ZMod.natCast_self, zero_add]
    rw [heq, ZMod.val_natCast_of_lt hlt]

/-- A number lying between two successive powers of two has its boundary bit
set. -/
theorem testBit_eq_true_of_two_pow_le_of_lt_two_pow_succ
    {x n : Nat} (hlo : 2 ^ n ≤ x) (hi : x < 2 ^ (n + 1)) :
    x.testBit n = true := by
  have hdecomp :
      x % 2 ^ (n + 1) =
        x % 2 ^ n + (x.testBit n).toNat * 2 ^ n := by
    rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]
  rw [Nat.mod_eq_of_lt hi] at hdecomp
  by_contra hne
  have hfalse : x.testBit n = false :=
    Bool.eq_false_of_not_eq_true hne
  rw [hfalse] at hdecomp
  simp only [Bool.toNat_false, zero_mul, Nat.add_zero] at hdecomp
  have hmodlt : x % 2 ^ n < 2 ^ n :=
    Nat.mod_lt x (Nat.two_pow_pos n)
  omega

theorem sum_lt_wordModulus {n N a b : Nat}
    (hN : N ≤ 2 ^ n) (ha : a < N) (hb : b < N) :
    a + b < 2 ^ (n + 1) := by
  have _hpowpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [pow_succ]
  omega

theorem modulus_lt_wordModulus {n N : Nat}
    (_hNpos : 0 < N) (hN : N ≤ 2 ^ n) :
    N < 2 ^ (n + 1) := by
  have _hpowpos : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [pow_succ]
  omega

/-- The high bit after subtracting the modulus is exactly the underflow bit. -/
theorem subtractModulus_msb {n N a b : Nat}
    (hN : N ≤ 2 ^ n) (ha : a < N) (hb : b < N) :
    (((((a + b : Nat) : ZMod (2 ^ (n + 1))) -
          (N : ZMod (2 ^ (n + 1)))).val).testBit n) =
      decide (a + b < N) := by
  have hNpos : 0 < N := by omega
  have hsB : a + b < 2 ^ (n + 1) := sum_lt_wordModulus hN ha hb
  have hNB : N < 2 ^ (n + 1) := modulus_lt_wordModulus hNpos hN
  rw [zmodVal_natCast_sub_natCast hsB hNB]
  by_cases h : N ≤ a + b
  · rw [if_pos h]
    have hlow : a + b - N < 2 ^ n := by omega
    rw [Nat.testBit_lt_two_pow hlow]
    simp [Nat.not_lt_of_ge h]
  · have hlt : a + b < N := Nat.lt_of_not_ge h
    rw [if_neg h]
    have hlo : 2 ^ n ≤ 2 ^ (n + 1) + (a + b) - N := by
      have _hpowpos : 0 < 2 ^ n := Nat.two_pow_pos n
      rw [pow_succ]
      omega
    have hi : 2 ^ (n + 1) + (a + b) - N < 2 ^ (n + 1) := by
      omega
    rw [testBit_eq_true_of_two_pow_le_of_lt_two_pow_succ hlo hi]
    simp [hlt]

/-- The subtraction high bit for an arbitrary one-word input below twice the
modulus.  Unlike `subtractModulus_msb`, this form does not require the input to
already be presented as a sum of two canonical residues. -/
theorem subtractModulusRaw_msb {n N s : Nat}
    (hNpos : 0 < N) (hN : N < 2 ^ n) (hs : s < 2 * N) :
    (((((s : Nat) : ZMod (2 ^ (n + 1))) -
          (N : ZMod (2 ^ (n + 1)))).val).testBit n) =
      decide (s < N) := by
  have hsB : s < 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  have hNB : N < 2 ^ (n + 1) :=
    modulus_lt_wordModulus hNpos (Nat.le_of_lt hN)
  rw [zmodVal_natCast_sub_natCast hsB hNB]
  by_cases h : N ≤ s
  · rw [if_pos h]
    have hlow : s - N < 2 ^ n := by omega
    rw [Nat.testBit_lt_two_pow hlow]
    simp [Nat.not_lt_of_ge h]
  · have hlt : s < N := Nat.lt_of_not_ge h
    rw [if_neg h]
    have hlo : 2 ^ n ≤ 2 ^ (n + 1) + s - N := by
      rw [pow_succ]
      omega
    have hi : 2 ^ (n + 1) + s - N < 2 ^ (n + 1) := by
      omega
    rw [testBit_eq_true_of_two_pow_le_of_lt_two_pow_succ hlo hi]
    simp [hlt]

/-- Word equality behind the add-back stage. -/
theorem addBack_word_eq_reduceOnce {n N a b : Nat} :
    (((a + b : Nat) : ZMod (2 ^ (n + 1))) -
        (N : ZMod (2 ^ (n + 1)))) +
      (if N ≤ a + b then 0 else (N : ZMod (2 ^ (n + 1)))) =
        (reduceOnce N (a + b) : ZMod (2 ^ (n + 1))) := by
  by_cases hreduce : N ≤ a + b
  · rw [reduceOnce, if_pos hreduce, if_pos hreduce, Nat.cast_sub hreduce]
    simp
  · rw [reduceOnce, if_neg hreduce, if_neg hreduce]
    ring

/-- The add-back stage has the ordinary representative produced by one
conditional subtraction. -/
theorem addBack_eq_reduceOnce {n N a b : Nat}
    (hN : N ≤ 2 ^ n) (ha : a < N) (hb : b < N) :
    ((((a + b : Nat) : ZMod (2 ^ (n + 1))) -
          (N : ZMod (2 ^ (n + 1))) +
        (if N ≤ a + b then 0 else (N : ZMod (2 ^ (n + 1))))).val) =
      reduceOnce N (a + b) := by
  have hNpos : 0 < N := by omega
  have hsB : a + b < 2 ^ (n + 1) := sum_lt_wordModulus hN ha hb
  have hNB : N < 2 ^ (n + 1) := modulus_lt_wordModulus hNpos hN
  by_cases h : N ≤ a + b
  · simp only [if_pos h, add_zero, reduceOnce]
    rw [ZMod.val_sub]
    · rw [ZMod.val_cast_of_lt hsB, ZMod.val_cast_of_lt hNB]
    · simpa only [ZMod.val_cast_of_lt hsB, ZMod.val_cast_of_lt hNB] using h
  · simp only [if_neg h, reduceOnce]
    rw [sub_add_cancel, ZMod.val_cast_of_lt hsB]

theorem addBack_eq_mod {n N a b : Nat}
    (hN : N ≤ 2 ^ n) (ha : a < N) (hb : b < N) :
    ((((a + b : Nat) : ZMod (2 ^ (n + 1))) -
          (N : ZMod (2 ^ (n + 1))) +
        (if N ≤ a + b then 0 else (N : ZMod (2 ^ (n + 1))))).val) =
      (a + b) % N := by
  rw [addBack_eq_reduceOnce hN ha hb]
  exact reduceOnce_eq_mod (by omega) (by omega)

/-- The high bit exposed by subtracting the original addend from the reduced
result is exactly the stored reduction flag, so the final CNOT clears it. -/
theorem cleanupProbe_msb {n N a b : Nat}
    (hN : N ≤ 2 ^ n) (ha : a < N) (hb : b < N) :
    (((((reduceOnce N (a + b) : Nat) : ZMod (2 ^ (n + 1))) -
          (a : ZMod (2 ^ (n + 1)))).val).testBit n) =
      decide (N ≤ a + b) := by
  have hNpos : 0 < N := by omega
  have hNB : N < 2 ^ (n + 1) := modulus_lt_wordModulus hNpos hN
  have haB : a < 2 ^ (n + 1) := ha.trans hNB
  unfold reduceOnce
  by_cases h : N ≤ a + b
  · rw [if_pos h]
    have hrN : a + b - N < N := by omega
    have hrB : a + b - N < 2 ^ (n + 1) := hrN.trans hNB
    have hra : a + b - N < a := by omega
    rw [zmodVal_natCast_sub_natCast hrB haB,
      if_neg (Nat.not_le_of_gt hra)]
    have hlo : 2 ^ n ≤ 2 ^ (n + 1) + (a + b - N) - a := by
      have _hpowpos : 0 < 2 ^ n := Nat.two_pow_pos n
      rw [pow_succ]
      omega
    have hi : 2 ^ (n + 1) + (a + b - N) - a < 2 ^ (n + 1) := by
      omega
    rw [testBit_eq_true_of_two_pow_le_of_lt_two_pow_succ hlo hi]
    simp [h]
  · have hsN : a + b < N := Nat.lt_of_not_ge h
    have hsB : a + b < 2 ^ (n + 1) := hsN.trans hNB
    rw [if_neg h]
    have haSum : a ≤ a + b := Nat.le_add_right a b
    rw [zmodVal_natCast_sub_natCast hsB haB, if_pos haSum]
    rw [Nat.add_sub_cancel_left]
    have hbLow : b < 2 ^ n := hb.trans_le hN
    rw [Nat.testBit_lt_two_pow hbLow]
    simp [h]

end VBEArithmetic
end MAU.Addition
end QuantumAlg

end
