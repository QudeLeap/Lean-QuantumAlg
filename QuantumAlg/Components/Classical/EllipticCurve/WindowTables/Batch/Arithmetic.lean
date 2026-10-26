/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Arithmetic
import Mathlib.Data.ZMod.Basic

/-!
# Field interpretation of the literal batch multiply value

The actual widened stored modulus gives a canonical finite-word result and
the original residue-ring product. No field operation is inserted into the
runtime circuit; these equations interpret its existing paid multiply.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Modular.NativePower

variable {width : Nat}

/-- The existing native multiply gives the original ring product at the actual loaded modulus. -/
lemma multiplyValue_cast (spec : ModulusSpec width) (left right : CShape.Word width) :
    ((multiplyValue left right (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) =
      (left.toNat : ZMod spec.modulus) * right.toNat := by
  rw [nativePower_multiplyValue_spec, ZMod.natCast_mod, Nat.cast_mul]

/-- Every result of that same actual multiply is canonical in the original modulus. -/
lemma multiplyValue_canonical (spec : ModulusSpec width) (left right : CShape.Word width) :
    (multiplyValue left right (.unsignedWord spec.extendedWord)).toNat < spec.modulus := by
  rw [nativePower_multiplyValue_spec]
  exact Nat.mod_lt _ (modulusSpec_modulus_pos spec)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
