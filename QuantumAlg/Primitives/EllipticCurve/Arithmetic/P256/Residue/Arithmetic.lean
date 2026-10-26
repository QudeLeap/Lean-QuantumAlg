/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Correctness
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Product
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Arithmetic
import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Program

/-!
# Field values of the original native arithmetic word endpoints

The actual modular-sum, Horner-product, accumulator-difference and
reflection endpoint functions use the original ordinary finite words.
These equations identify those exact numerical results with their field
values. They do not add an arithmetic operation or change a circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue

noncomputable section

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

lemma sum_word (left right : ZMod modulus) :
    ModularAddition.modularSumWord (word left) (word right) = word (left + right) := by
  apply Fin.ext
  exact (ZMod.val_add left right).symm

lemma product_word (source multiplier : ZMod modulus) (selected : Bool) :
    Horner.productWord (word source) (word multiplier) selected =
      word (if selected then multiplier * source else 0) := by
  cases selected with
  | false => exact word_zero.symm
  | true =>
      apply Fin.ext
      exact (ZMod.val_mul multiplier source).symm

lemma accumulated_word (source multiplier target : ZMod modulus) :
    Accumulate.accumulatedWord (word source) (word multiplier) (word target) true =
      word (target + source * multiplier) := by
  apply Fin.ext
  change (target.val + source.val * multiplier.val) % modulus =
    (target + source * multiplier).val
  rw [ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod]

lemma difference_word (source multiplier target : ZMod modulus) :
    Accumulate.Inverse.differenceWord (word source) (word multiplier) (word target) true =
      word (target - source * multiplier) := by
  have canonical := Accumulate.Inverse.differenceWord_canonical
    (word source) (word multiplier) (word target) true (word_canonical target)
  rw [eq_word _ canonical]
  apply congrArg word
  change (((target.val + modulus - (source.val * multiplier.val) % modulus) % modulus : Nat) :
    ZMod modulus) = target - source * multiplier
  have below : (source.val * multiplier.val) % modulus ≤ target.val + modulus := by
    have limit := Nat.mod_lt (source.val * multiplier.val) modulus_positive
    omega
  rw [ZMod.natCast_mod, Nat.cast_sub below, Nat.cast_add, ZMod.natCast_self, add_zero,
    ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

/-- The real canonical reflection is exactly the field operation preceding the Qx+1 column. -/
lemma reflected_word (value : ZMod modulus) :
    MAU.Addition.TTK.Reflection.reflected (width := 256)
      ⟨modulus, modulus_lt_capacity⟩ (word value) = word (-1 - value) := by
  have canonical := ZMod.val_lt value
  have modulusNonzero := modulus_positive
  have represented : ((modulus - 1 - value.val : Nat) : ZMod modulus) = -1 - value := by
    rw [Nat.cast_sub (by omega : value.val ≤ modulus - 1),
      Nat.cast_sub (by omega : 1 ≤ modulus), ZMod.natCast_self, Nat.cast_one,
      ZMod.natCast_zmod_val, zero_sub]
  have bounded : modulus - 1 - value.val < modulus := by omega
  have same := congrArg ZMod.val represented
  rw [ZMod.val_natCast_of_lt bounded] at same
  apply Fin.ext
  exact (MAU.Addition.TTK.Reflection.reflected_value
    (⟨modulus, modulus_lt_capacity⟩ : Fin (2 ^ 256)) (word value)
    (word_canonical value)).trans same

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue
