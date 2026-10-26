/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Arithmetic

/-!
# Field values of the actual shared-modulus row arithmetic

These equations interpret the literal finite-word operations. Subtraction's
canonical-right domain is explicit; all computed results are canonical. The
actual executable slots continue to read the same loaded modulus and Store.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular Field.Native.Shared

variable {width : Nat}

/-- The actual five-operation addition represents the field sum of its original operands. -/
lemma addValue_cast (spec : ModulusSpec width) (left right : CShape.Word width) :
    ((addValue left right (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) =
      (left.toNat : ZMod spec.modulus) + right.toNat := by
  rw [addValue_toNat left right (.unsignedWord spec.extendedWord)
    (modulusSpec_modulus_pos spec) spec.le_capacity]
  change (((left.toNat + right.toNat) % spec.modulus : Nat) : ZMod spec.modulus) = _
  rw [ZMod.natCast_mod, Nat.cast_add]

/-- The same actual addition returns a canonical finite word. -/
lemma addValue_canonical (spec : ModulusSpec width) (left right : CShape.Word width) :
    (addValue left right (.unsignedWord spec.extendedWord)).toNat < spec.modulus := by
  rw [addValue_toNat left right (.unsignedWord spec.extendedWord)
    (modulusSpec_modulus_pos spec) spec.le_capacity]
  exact Nat.mod_lt _ (modulusSpec_modulus_pos spec)

/-- Actual subtraction agrees with the original field difference on its real no-borrow domain. -/
lemma subValue_cast (spec : ModulusSpec width) (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    ((subValue left right (.unsignedWord spec.extendedWord)).toNat : ZMod spec.modulus) =
      (left.toNat : ZMod spec.modulus) - right.toNat := by
  have noBorrow : right.toNat ≤ left.toNat + spec.modulus := by omega
  rw [subValue_toNat spec left right (.unsignedWord spec.extendedWord) rfl rightCanonical,
    ZMod.natCast_mod, Nat.cast_sub noBorrow, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- On that same domain the literal subtraction returns a canonical finite word. -/
lemma subValue_canonical (spec : ModulusSpec width) (left right : CShape.Word width)
    (rightCanonical : right.toNat < spec.modulus) :
    (subValue left right (.unsignedWord spec.extendedWord)).toNat < spec.modulus := by
  rw [subValue_toNat spec left right (.unsignedWord spec.extendedWord) rfl rightCanonical]
  exact Nat.mod_lt _ (modulusSpec_modulus_pos spec)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
