/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Binary-prefix mathematics for modular multiply-accumulate

These quantum-free identities describe scanning a multiplier from least
significant to most significant bit. They impose no parity or unit-coefficient
condition and include modulus one and zero coefficients. Stage `i` conditionally
adds the fixed residue
`a * 2^i mod N`; after the first `k` stages, the selected binary weight is the
low-`k`-bit prefix of the multiplier.  This is the arithmetic recurrence behind
the controlled modular-add construction in [VBE95, 9511018.tex:333-367].
-/

section

namespace QuantumAlg
namespace Nat.FixedWidth.ModularAccumulate

/-- Natural-number weight selected by bit `i` of `x`. -/
def selectedBitWeight (x i : Nat) : Nat :=
  (x.testBit i).toNat * 2 ^ i

/-- Sum of the binary weights selected by the first `k` bits of `x`. -/
def selectedLowWeight (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => selectedLowWeight x k + selectedBitWeight x k

@[simp] theorem selectedLowWeight_zero (x : Nat) :
    selectedLowWeight x 0 = 0 :=
  rfl

@[simp] theorem selectedLowWeight_succ (x k : Nat) :
    selectedLowWeight x (k + 1) =
      selectedLowWeight x k + selectedBitWeight x k :=
  rfl

/-- The selected weight is either zero or the corresponding power of two. -/
theorem selectedBitWeight_eq_if (x i : Nat) :
    selectedBitWeight x i = if x.testBit i then 2 ^ i else 0 := by
  cases hbit : x.testBit i <;> simp [selectedBitWeight, hbit]

/-- Low-bit decomposition at the next power of two. -/
theorem selectedLowWeight_mod_two_pow_succ_decomp (x i : Nat) :
    x % 2 ^ (i + 1) =
      x % 2 ^ i + (x.testBit i).toNat * 2 ^ i := by
  rw [Nat.mod_pow_succ, Nat.toNat_testBit, Nat.mul_comm]

/-- The first `k` selected binary weights are exactly the low-`k`-bit prefix
of `x`. -/
theorem selectedLowWeight_eq_mod_two_pow (x k : Nat) :
    selectedLowWeight x k = x % 2 ^ k := by
  induction k with
  | zero =>
      exact (Nat.mod_one x).symm
  | succ k ih =>
      rw [selectedLowWeight_succ, ih, selectedBitWeight,
        selectedLowWeight_mod_two_pow_succ_decomp]

/-- Reading every bit of an `n`-bit value reconstructs the value itself. -/
theorem selectedLowWeight_eq_self_of_lt_two_pow
    {x n : Nat} (hx : x < 2 ^ n) :
    selectedLowWeight x n = x := by
  rw [selectedLowWeight_eq_mod_two_pow, Nat.mod_eq_of_lt hx]

/-- Fixed modular residue loaded at stage `i`, independently of the runtime
multiplier bit. -/
def stageConstantResidue (N a i : Nat) : Nat :=
  (a * 2 ^ i) % N

/-- The arithmetic residue agrees with the circuit-facing `2^i * a` order. -/
theorem stageConstantResidue_eq_pow_mul (N a i : Nat) :
    stageConstantResidue N a i = (2 ^ i * a) % N := by
  rw [stageConstantResidue, Nat.mul_comm]

/-- Contribution of stage `i` after it is selected by bit `i` of `x`. -/
def selectedBitContribution (N a x i : Nat) : Nat :=
  (a * selectedBitWeight x i) % N

/-- The selected contribution is the fixed stage constant when the controlling
multiplier bit is set, and zero otherwise. -/
theorem selectedBitContribution_eq_if (N a x i : Nat) :
    selectedBitContribution N a x i =
      if x.testBit i then stageConstantResidue N a i else 0 := by
  cases hbit : x.testBit i <;>
    simp [selectedBitContribution, selectedBitWeight, stageConstantResidue,
      hbit]

/-- Every stage constant is a canonical residue for a positive modulus. -/
theorem stageConstantResidue_lt {N a i : Nat} (hN : 0 < N) :
    stageConstantResidue N a i < N :=
  Nat.mod_lt _ hN

/-- Every selected stage contribution is a canonical residue for a positive
modulus. -/
theorem selectedBitContribution_lt {N a x i : Nat} (hN : 0 < N) :
    selectedBitContribution N a x i < N :=
  Nat.mod_lt _ hN

/-- Accumulate the first `k` selected stage contributions modulo `N`, starting
from accumulator `y`.  The recursive order is least significant bit first,
matching a bit-controlled modular accumulation. -/
def accumulateSelected (N a x y : Nat) : Nat → Nat
  | 0 => y % N
  | k + 1 =>
      (accumulateSelected N a x y k +
        selectedBitContribution N a x k) % N

@[simp] theorem accumulateSelected_zero (N a x y : Nat) :
    accumulateSelected N a x y 0 = y % N :=
  rfl

@[simp] theorem accumulateSelected_succ (N a x y k : Nat) :
    accumulateSelected N a x y (k + 1) =
      (accumulateSelected N a x y k +
        selectedBitContribution N a x k) % N :=
  rfl

/-- Every nonempty-modulus accumulator prefix is represented canonically. -/
theorem accumulateSelected_lt {N a x y k : Nat} (hN : 0 < N) :
    accumulateSelected N a x y k < N := by
  cases k with
  | zero =>
      exact Nat.mod_lt y hN
  | succ k =>
      exact Nat.mod_lt _ hN

/-- Prefix invariant for the bit-by-bit modular accumulation. -/
theorem accumulateSelected_eq_add_mul_selectedLowWeight_mod
    (N a x y k : Nat) :
    accumulateSelected N a x y k =
      (y + a * selectedLowWeight x k) % N := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      simp only [accumulateSelected_succ, ih, selectedBitContribution,
        selectedLowWeight_succ, Nat.mul_add, Nat.mod_add_mod,
        Nat.add_mod_mod, Nat.add_assoc]

/-- After `k` stages, the modular accumulator contains the product with the
low-`k`-bit prefix of `x`. -/
theorem accumulateSelected_eq_add_mul_mod_two_pow
    (N a x y k : Nat) :
    accumulateSelected N a x y k =
      (y + a * (x % 2 ^ k)) % N := by
  rw [accumulateSelected_eq_add_mul_selectedLowWeight_mod,
    selectedLowWeight_eq_mod_two_pow]

/-- Full-width endpoint: scanning all bits of an `n`-bit multiplier adds
`a * x` to the accumulator modulo `N`. -/
theorem accumulateSelected_eq_add_mul_mod_of_lt_two_pow
    {N a x y n : Nat} (hx : x < 2 ^ n) :
    accumulateSelected N a x y n = (y + a * x) % N := by
  rw [accumulateSelected_eq_add_mul_selectedLowWeight_mod,
    selectedLowWeight_eq_self_of_lt_two_pow hx]

/-- Zero-seeded prefix accumulation is the selected partial product modulo
`N`. -/
theorem accumulateSelected_zero_seed_eq_mul_mod
    (N a x k : Nat) :
    accumulateSelected N a x 0 k =
      (a * selectedLowWeight x k) % N := by
  simpa using
    accumulateSelected_eq_add_mul_selectedLowWeight_mod N a x 0 k

/-- Zero-seeded full-width accumulation is `a * x mod N`. -/
theorem accumulateSelected_zero_seed_eq_mul_mod_of_lt_two_pow
    {N a x n : Nat} (hx : x < 2 ^ n) :
    accumulateSelected N a x 0 n = (a * x) % N := by
  simpa using
    accumulateSelected_eq_add_mul_mod_of_lt_two_pow
      (N := N) (a := a) (x := x) (y := 0) hx

end Nat.FixedWidth.ModularAccumulate
end QuantumAlg

end
