/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Data.Int.ModEq

/-!
# Integer congruence of low-word multiplication and subtraction

The low-product and wrapping subtraction represent the exact integer
subtraction modulo the word capacity. All natural inputs and width zero
remain in the domain; no signed-range or runtime-state premise is imposed.
-/

namespace QuantumAlg.Nat.FixedWidth

public lemma lowMultiplySubtract_intModEq (width target coefficient source : Nat) :
    Int.ModEq (2 ^ width : Nat)
      (((target + 2 ^ width - (coefficient * source) % 2 ^ width) % 2 ^ width : Nat) : Int)
      ((target : Int) - (coefficient : Int) * (source : Int)) := by
  let capacity := 2 ^ width
  let lowProduct := (coefficient * source) % capacity
  have productBound : lowProduct ≤ target + capacity :=
    (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos width))).trans (Nat.le_add_left _ _)
  have lifted : ((target + capacity - lowProduct : Nat) : Int) =
      (target : Int) + (capacity : Int) - (lowProduct : Int) := by
    rw [Int.natCast_sub productBound, Int.natCast_add]
  have productMod : Int.ModEq (capacity : Int) (lowProduct : Int)
      ((coefficient : Int) * (source : Int)) := by
    have actual := Int.natCast_modEq_iff.mpr (Nat.mod_modEq (coefficient * source) capacity)
    simpa only [Int.natCast_mul] using actual
  have subtracted : Int.ModEq (capacity : Int)
      ((target + capacity - lowProduct : Nat) : Int)
      ((target : Int) - (coefficient : Int) * (source : Int)) := by
    rw [lifted]
    exact (Int.add_modEq_right (a := (target : Int)) (n := (capacity : Int))).sub productMod
  exact (Int.natCast_modEq_iff.mpr
    (Nat.mod_modEq (target + capacity - lowProduct) capacity)).trans subtracted

end QuantumAlg.Nat.FixedWidth
