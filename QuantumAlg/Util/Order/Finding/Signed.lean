/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Order.Finding
public import Mathlib.RingTheory.Int.Basic
import all QuantumAlg.Util.Order.Finding
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
# Signed modular bases for the source order-finding domain

An integer base is represented by its canonical modular residue. Reduction
preserves every modular power and the least positive order; it imposes no
nonnegativity restriction on the mathematical source input
[Sho95, source.tex:1124-1148]. These are mathematical representation laws,
not claims that computing a residue from an unbounded integer has zero cost.
-/

namespace QuantumAlg.OrderFinding

/-- The bounded natural representative retains the original signed residue. -/
public lemma orderFinding_signedResidue_cast {N : Nat} (positive : 0 < N) (x : Int) :
    (((x : ZMod N).val : Nat) : ZMod N) = (x : ZMod N) := by
  have : NeZero N := ⟨Nat.ne_of_gt positive⟩
  exact ZMod.natCast_zmod_val (x : ZMod N)

/-- Every exponent in the declared query has the original signed modular power. -/
public lemma orderFinding_signedResidue_power {N : Nat} (positive : 0 < N)
    (x : Int) (exponent : Nat) :
    (x : ZMod N).val ^ exponent % N = ((x : ZMod N) ^ exponent).val := by
  rw [← ZMod.val_natCast N ((x : ZMod N).val ^ exponent), Nat.cast_pow,
    orderFinding_signedResidue_cast positive x]

/-- Coprimality of an arbitrary signed base survives canonical representation. -/
public lemma orderFinding_signedResidue_coprime {N : Nat} (positive : 0 < N)
    (x : Int) (coprime : Nat.Coprime x.natAbs N) :
    Nat.Coprime (x : ZMod N).val N := by
  have integerCoprime : IsCoprime x (N : Int) :=
    Int.isCoprime_iff_nat_coprime.mpr (by simpa using coprime)
  have modularCoprime : IsCoprime (x : ZMod N) 0 := by
    simpa using integerCoprime.map (Int.castRingHom (ZMod N))
  have unit : IsUnit (x : ZMod N) := isCoprime_zero_right.mp modularCoprime
  apply (ZMod.isUnit_iff_coprime (x : ZMod N).val N).mp
  rw [orderFinding_signedResidue_cast positive x]
  exact unit

/-- The original signed source-order premises give the existing bounded-base
input, with the identical least positive order. -/
public lemma orderFinding_input_of_signedBase {N r : Nat} (modulus : 2 ≤ N)
    (x : Int) (coprime : Nat.Coprime x.natAbs N) (orderPositive : 0 < r)
    (returnsOne : (x : ZMod N) ^ r = 1)
    (minimal : ∀ m : Nat, 0 < m → (x : ZMod N) ^ m = 1 → r ≤ m) :
    Input N (x : ZMod N).val r := by
  have positive : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) modulus
  have oneSmall : 1 < N := lt_of_lt_of_le (by decide : 1 < 2) modulus
  refine ⟨modulus, orderFinding_signedResidue_coprime positive x coprime,
    orderPositive, ?_, ?_⟩
  · have castPower : (((x : ZMod N).val ^ r : Nat) : ZMod N) = ((1 : Nat) : ZMod N) := by
      simpa only [Nat.cast_pow, Nat.cast_one,
        orderFinding_signedResidue_cast positive x] using returnsOne
    have congruence := (ZMod.natCast_eq_natCast_iff ((x : ZMod N).val ^ r) 1 N).mp castPower
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt oneSmall] using congruence
  · intro m mPositive modularPower
    apply minimal m mPositive
    have congruence : (x : ZMod N).val ^ m ≡ 1 [MOD N] := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt oneSmall] using modularPower
    have castPower :=
      (ZMod.natCast_eq_natCast_iff ((x : ZMod N).val ^ m) 1 N).mpr congruence
    simpa only [Nat.cast_pow, Nat.cast_one,
      orderFinding_signedResidue_cast positive x] using castPower

end QuantumAlg.OrderFinding
