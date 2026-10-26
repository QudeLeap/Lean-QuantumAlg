/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Inversion

/-!
# The same ordinary field word in the original resident input carrier

The resident input uses modulus.size bits and the physical payload uses
256 bits. The existing size identity transports this mathematical label
without an instruction, a new encoding, or a new source initialization.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue

noncomputable section

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

attribute [local irreducible] modulus

/-- The ordinary canonical word in the original resident input type. -/
def input (value : ZMod modulus) : Fin (2 ^ modulus.size) :=
  Fin.cast (congrArg (fun size => 2 ^ size) Point.Inversion.modulus_size).symm (word value)

lemma cast_input (value : ZMod modulus) :
    Fin.cast (congrArg (fun size => 2 ^ size) Point.Inversion.modulus_size) (input value) =
      word value := by
  apply Fin.ext
  rfl

lemma input_val (value : ZMod modulus) : (input value).val = value.val := rfl

lemma input_cast (value : ZMod modulus) : ((input value).val : ZMod modulus) = value :=
  word_cast value

lemma input_bounded (value : ZMod modulus) : (input value).val < modulus :=
  ZMod.val_lt value

lemma input_positive (value : ZMod modulus) (nonzero : value ≠ 0) :
    0 < (input value).val :=
  Nat.pos_of_ne_zero (fun zero => nonzero ((ZMod.val_eq_zero value).mp zero))

lemma input_coprime [Fact modulus.Prime] (value : ZMod modulus) (nonzero : value ≠ 0) :
    Nat.Coprime (input value).val modulus := by
  apply Nat.Coprime.symm
  apply (Fact.out : Nat.Prime modulus).coprime_iff_not_dvd.mpr
  intro divides
  exact nonzero ((input_cast value).symm.trans
    ((ZMod.natCast_eq_zero_iff (input value).val modulus).mpr divides))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue
