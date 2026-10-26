/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Arithmetic

/-! # Canonical modular difference for the complete actual multiply-accumulate adjoint -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse

def differenceWord (source multiplier target : Word) (selected : Bool) : Word :=
  if selected then
    ⟨(target.val + modulus - (source.val * multiplier.val) % modulus) % modulus,
      (Nat.mod_lt _ modulus_positive).trans modulus_lt_capacity⟩
  else target

lemma differenceWord_canonical (source multiplier target : Word) (selected : Bool)
    (canonical : Canonical target) : Canonical (differenceWord source multiplier target selected) :=
  by cases selected with
  | false => exact canonical
  | true => exact Nat.mod_lt _ modulus_positive

private lemma add_difference {modulus target product : Nat}
    (canonical : target < modulus) (productBound : product % modulus < modulus) :
    ((target + modulus - product % modulus) % modulus + product) % modulus = target := by
  calc
    _ = ((target + modulus - product % modulus) % modulus + product % modulus) % modulus :=
      (Nat.add_mod_mod _ _ _).symm
    _ = target := by
      rw [Nat.mod_add_mod, Nat.sub_add_cancel (by omega), Nat.add_mod_right,
        Nat.mod_eq_of_lt canonical]

/-- Forward MAC of the modular difference returns every original canonical accumulator. -/
lemma accumulated_difference (source multiplier target : Word) (selected : Bool)
    (canonical : Canonical target) :
    accumulatedWord source multiplier (differenceWord source multiplier target selected)
      selected = target := by
  cases selected with
  | false => rfl
  | true =>
      apply Fin.ext
      exact add_difference canonical (Nat.mod_lt _ modulus_positive)

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse
