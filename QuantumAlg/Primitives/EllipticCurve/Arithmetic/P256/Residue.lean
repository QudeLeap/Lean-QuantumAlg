/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import Mathlib.Data.ZMod.Basic

/-!
# Canonical field values in the original ordinary P-256 word

This mathematical coordinate map uses the same original binary payload.
It introduces no circuit or conversion operation. Canonical word equality
is equivalent to equality of the represented field values; padded binary
words retain their separate, existing inactive-sector contracts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue

noncomputable section

local instance : NeZero modulus := ⟨Nat.ne_of_gt modulus_positive⟩

/-- A field value has its ordinary canonical residue in the original physical word. -/
def word (value : ZMod modulus) : Word :=
  ⟨value.val, (ZMod.val_lt value).trans modulus_lt_capacity⟩

lemma word_val (value : ZMod modulus) : (word value).val = value.val := rfl

lemma word_cast (value : ZMod modulus) : ((word value).val : ZMod modulus) = value :=
  ZMod.natCast_zmod_val value

lemma word_canonical (value : ZMod modulus) : Canonical (word value) := ZMod.val_lt value

lemma word_injective : Function.Injective word := by
  intro first second same
  exact ZMod.val_injective modulus (congrArg (fun value : Word => value.val) same)

lemma word_zero : word 0 = (⟨0, Nat.two_pow_pos width⟩ : Word) := by
  apply Fin.ext
  change (0 : ZMod modulus).val = 0
  exact ZMod.val_zero

/-- This coordinate equality requires exactly the original canonical-residue premise. -/
lemma eq_word (value : Word) (canonical : Canonical value) :
    value = word (value.val : ZMod modulus) := by
  apply Fin.ext
  exact (ZMod.val_natCast_of_lt canonical).symm

/-- A canonical physical word is zero precisely when its represented field value is zero. -/
lemma cast_eq_zero_iff (value : Word) (canonical : Canonical value) :
    (value.val : ZMod modulus) = 0 ↔ value.val = 0 := by
  constructor
  · intro zero
    have actual := congrArg ZMod.val zero
    simpa only [ZMod.val_natCast_of_lt canonical, ZMod.val_zero] using actual
  · intro zero
    rw [zero, Nat.cast_zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Residue
