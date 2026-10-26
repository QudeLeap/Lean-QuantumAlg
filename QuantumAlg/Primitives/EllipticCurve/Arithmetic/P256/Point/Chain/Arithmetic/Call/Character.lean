/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Parameters
import all QuantumAlg.Util.NumberTheory.SharedEEA.InverseOutput.Canonical
import all Mathlib.Data.Nat.ModEq

/-!
# Arithmetic cancellation of the actual saved-word phase character

Both measured calls use the same saved-word definition as their real Save
and Phase programs. Cancellation needs canonical numerators only when the
actual selector is true. Inactive numerators keep their entire binary value.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

/-- The actual signed EEA output transported to the original point payload word. -/
def inverseWord (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val)
    (bounded : input.val < modulus) : Word :=
  Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size)
    (NumberTheory.SharedEEA.InverseOutput.word modulus input.val positive bounded)

lemma inverseWord_canonical (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) : Canonical (inverseWord input positive bounded) :=
  NumberTheory.SharedEEA.InverseOutput.word_lt_modulus modulus input.val
    Inversion.modulus_nontrivial coprime positive bounded

lemma inverseWord_product (input : Fin (2 ^ modulus.size))
    (coprime : Nat.Coprime input.val modulus) (positive : 0 < input.val)
    (bounded : input.val < modulus) :
    Nat.ModEq modulus (input.val * (inverseWord input positive bounded).val) 1 := by
  change Nat.ModEq modulus
    (input.val * (NumberTheory.SharedEEA.InverseOutput.word modulus input.val
      positive bounded).val) 1
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa only [Nat.cast_mul, Nat.cast_one] using
    NumberTheory.SharedEEA.InverseOutput.word_product modulus input.val coprime positive bounded

private lemma residue_cancel (modulus first second numerator : Nat)
    (inverse : Nat.ModEq modulus (first * second) 1) (canonical : numerator < modulus) :
    (((numerator * second) % modulus) * first) % modulus = numerator := by
  rw [Nat.mod_mul_mod]
  calc
    (numerator * second * first) % modulus = (numerator * (first * second)) % modulus := by
      apply congrArg (fun value => value % modulus)
      ac_rfl
    _ = (numerator * 1) % modulus := inverse.mul_left numerator
    _ = numerator := by rw [Nat.mul_one, Nat.mod_eq_of_lt canonical]

/-- The same identity covers division and multiplication, including coherent inactive labels. -/
lemma savedWord_cancel (first second numerator : Word) (selected : Bool)
    (inverse : selected = true → Nat.ModEq modulus (first.val * second.val) 1)
    (canonical : selected = true → Canonical numerator) :
    Save.savedWord first (Save.savedWord second numerator selected) selected = numerator := by
  cases selected with
  | false => rfl
  | true =>
      apply Fin.ext
      change (((numerator.val * second.val) % modulus) * first.val) % modulus = numerator.val
      exact residue_cancel modulus first.val second.val numerator.val (inverse rfl) (canonical rfl)

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
