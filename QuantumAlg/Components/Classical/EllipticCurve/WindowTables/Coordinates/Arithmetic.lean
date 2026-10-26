/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Arithmetic

/-!
# Finite word of the actual raw coefficient slot

The original total XGCD coefficient is reduced into the same finite word
written by the actual slot. Only its canonical nonzero original input
domain identifies this paid result with a field inverse. No mathematical
inverse operation is added to any row program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open ClassicalAlgorithms.Modular

noncomputable section

variable {width : Nat}

/-- Literal finite-word value written by the original actual coefficient slot. -/
def coefficientWordValue (spec : ModulusSpec width) (input : CShape.Word width) :
    CShape.Word width :=
  CShape.wordOfNat width (Field.Native.coefficientResidue spec input).val

/-- The actual residue always fits the original result word without narrowing loss. -/
lemma coefficientWordValue_toNat (spec : ModulusSpec width) (input : CShape.Word width) :
    (coefficientWordValue spec input).toNat = (Field.Native.coefficientResidue spec input).val :=
  Nat.mod_eq_of_lt (lt_of_lt_of_le (Field.Native.coefficientResidue spec input).isLt
    spec.le_capacity)

/-- That same total coefficient word is canonical even when the raw input is a non-unit. -/
lemma coefficientWordValue_canonical (spec : ModulusSpec width) (input : CShape.Word width) :
    (coefficientWordValue spec input).toNat < spec.modulus := by
  rw [coefficientWordValue_toNat]
  exact (Field.Native.coefficientResidue spec input).isLt

/-- A locally canonical nonzero original denominator makes that same raw result its inverse. -/
lemma coefficientWordValue_cast_eq_inv (spec : ModulusSpec width) [Fact spec.modulus.Prime]
    (input : CShape.Word width) (canonical : input.toNat < spec.modulus)
    (nonzero : (input.toNat : ZMod spec.modulus) ≠ 0) :
    ((coefficientWordValue spec input).toNat : ZMod spec.modulus) =
      (input.toNat : ZMod spec.modulus)⁻¹ := by
  let _ : NeZero spec.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  have represented : input.toNat = (input.toNat : ZMod spec.modulus).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt canonical]
  rw [coefficientWordValue_toNat]
  exact Field.Native.coefficientResidue_cast_eq_inv spec input _ represented
    (isUnit_iff_ne_zero.mpr nonzero)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
