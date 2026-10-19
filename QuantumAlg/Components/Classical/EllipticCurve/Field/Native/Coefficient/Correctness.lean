/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Interpretation

/-!
# Original coefficient and local field-inverse interpretation

The actual total coefficient agrees with the original pure engine on its
canonical denominator domain. A local unit proof then identifies that same
returned coefficient with the field inverse. The executable program contains
no unit witness, gcd-success branch, or replacement inverse operation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular
open NumberTheory.Checked.SignedReduction

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The actual total residue is the original deterministic pure engine coefficient. -/
lemma coefficientResidue_eq_inverseCoefficient (spec : ModulusSpec width)
    (raw : CShape.Word width) (denominator : Residue spec)
    (represented : raw.toNat = denominator.val) :
    coefficientResidue spec raw =
      NumberTheory.Checked.Engine.inverseCoefficient spec denominator := by
  unfold coefficientResidue
  rw [NumberTheory.Checked.Native.widenedXgcdInput_eq_xgcdInput spec
    (CShape.wordOfNat (width + 1) spec.modulus) raw denominator
    (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec)) represented]
  apply congrArg (residueOfInt spec)
  exact (ClassicalAlgorithms.NumberTheory.XGCD.xgcdFinalState_resultRightCoefficient_eq_gcdB
    (NumberTheory.Checked.Engine.xgcdInput spec denominator)).trans
      (ClassicalAlgorithms.NumberTheory.XGCD.xgcdEval_rightCoefficient_toInt
        (NumberTheory.Checked.Engine.xgcdInput spec denominator)).symm

/-- Original canonical denominators give the original engine value in the actual output cell. -/
lemma fieldCoefficient_output_eq_original (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (hidden : model.HiddenState)
    (semantic : Residue spec) (represented : (store.read denominator).toNat = semantic.val) :
    ((coefficientIntoWordStep (environment := environment) spec denominator output (store,
      hidden)).1.1.read
      (coefficientRead output)).toNat =
        (NumberTheory.Checked.Engine.inverseCoefficient spec semantic).val := by
  rw [coefficientIntoWord_toNat,
    coefficientResidue_eq_inverseCoefficient spec (store.read denominator) semantic represented]

/-- A locally selected unit makes this same total coefficient equal the field inverse. -/
lemma coefficientResidue_cast_eq_inv (spec : ModulusSpec width)
    (raw : CShape.Word width) (value : ZMod spec.modulus)
    (represented : raw.toNat = value.val) (unit : IsUnit value) :
    ((coefficientResidue spec raw).val : ZMod spec.modulus) = value⁻¹ := by
  let _ : NeZero spec.modulus := ⟨Nat.ne_of_gt (modulusSpec_modulus_pos spec)⟩
  let semantic : Residue spec := ⟨value.val, ZMod.val_lt value⟩
  have coprime : Nat.Coprime semantic.val spec.modulus := by
    apply (ZMod.isUnit_iff_coprime value.val spec.modulus).mp
    simpa only [ZMod.natCast_zmod_val] using unit
  rw [coefficientResidue_eq_inverseCoefficient spec raw semantic represented,
    NumberTheory.Checked.Engine.inverseCoefficient_eq_candidate spec semantic coprime]
  change (((value.val : ZMod spec.modulus)⁻¹).val : ZMod spec.modulus) = value⁻¹
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The real output cell is the inverse exactly on the original locally proved unit domain. -/
lemma fieldCoefficient_output_inverse (spec : ModulusSpec width)
    (denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (hidden : model.HiddenState)
    (value : ZMod spec.modulus) (represented : (store.read denominator).toNat = value.val)
    (unit : IsUnit value) :
    (((coefficientIntoWordStep (environment := environment) spec denominator output (store,
      hidden)).1.1.read
      (coefficientRead output)).toNat : ZMod spec.modulus) = value⁻¹ := by
  rw [coefficientIntoWord_toNat]
  exact coefficientResidue_cast_eq_inv spec (store.read denominator) value represented unit

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
