/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Character
import Mathlib.Algebra.Field.ZMod

/-!
# Ordinary field value of the actual signed-EEA inverse word

The inverse is the original resident EEA's canonical, corrected output.
Its accepted product identity identifies that same finite word with the
field inverse on precisely its original positive, bounded, coprime input
domain. The actual Save endpoint then gives ordinary field division.
No new inverse operation or classical preprocessing is executed here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue

noncomputable section

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

open Point.Chain.Arithmetic

/-- Canonical inverse-word equality follows from that actual EEA output's product identity. -/
lemma inverse_word [Fact modulus.Prime] (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) :
    Call.inverseWord input positive bounded = word ((input.val : ZMod modulus)⁻¹) := by
  refine (eq_word _ (Call.inverseWord_canonical input coprime positive bounded)).trans ?_
  apply congrArg word
  have product : (input.val : ZMod modulus) *
      ((Call.inverseWord input positive bounded).val : ZMod modulus) = 1 := by
    have actual := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
      (Call.inverseWord_product input coprime positive bounded)
    simpa only [Nat.cast_mul, Nat.cast_one] using actual
  have nonzero : (input.val : ZMod modulus) ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at product
    exact zero_ne_one product
  exact mul_left_cancel₀ nonzero (product.trans (mul_inv_cancel₀ nonzero).symm)

/-- Both actual Save branches use the same canonical coordinates, with the disabled Y retained. -/
lemma saved_word (source numerator : ZMod modulus) (selected : Bool) :
    Save.savedWord (word source) (word numerator) selected =
      word (if selected then numerator * source else numerator) := by
  cases selected with
  | false => rfl
  | true => exact product_word source numerator true

/-- The active actual saved product of the EEA inverse is the original secant quotient. -/
lemma saved_division_word [Fact modulus.Prime] (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) (numerator : ZMod modulus) :
    Save.savedWord (Call.inverseWord input positive bounded) (word numerator) true =
      word (numerator / (input.val : ZMod modulus)) := by
  rw [inverse_word input coprime positive bounded, saved_word]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue
