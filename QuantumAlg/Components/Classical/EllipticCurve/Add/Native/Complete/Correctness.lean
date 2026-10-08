/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling.Correctness

/-!
# Original complete point addition from the actual native return

Canonical representations connect the actual tag and coordinate classifier to
all original cases: either infinity, inverse or vertical inputs, nonvertical
doubling, and distinct-coordinate addition. Each selected actual finite result
represents the original group-law sum. The existing total execution record
then gives that representation in the actual caller destination.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalAlgorithms.Modular ClassicalAlgorithms.EllipticCurve
open ClassicalAlgorithms.EllipticCurve.ShortWeierstrass

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem coordinateWord_eq_iff (spec : CurveSpec width)
    (x y : ZMod spec.field.modulus) :
    coordinateWord spec x = coordinateWord spec y ↔ x = y := by
  constructor
  · intro same
    have value := congrArg (fun word : Fin (2 ^ width) => (word.val : ZMod spec.field.modulus)) same
    simpa only [coordinateWord_val, ZMod.natCast_zmod_val] using value
  · rintro rfl
    rfl

private theorem coordinateWord_zero_iff (spec : CurveSpec width)
    (x : ZMod spec.field.modulus) : coordinateWord spec x = 0 ↔ x = 0 := by
  have zero : coordinateWord spec (0 : ZMod spec.field.modulus) = 0 := by
    apply Fin.ext
    simpa only [coordinateWord_val, Fin.val_zero] using
      (ZMod.val_zero (n := spec.field.modulus))
  rw [← zero]
  exact coordinateWord_eq_iff spec x 0

private theorem classifyValues_encoded_finite (spec : CurveSpec width)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂) :
    classifyValues (encodePoint spec (.some x₁ y₁ h₁))
      (encodePoint spec (.some x₂ y₂ h₂)) =
      if x₁ = x₂ then
        if y₁ = y₂ then if y₁ = 0 then .vertical else .doubling else .vertical
      else .generic := by
  simp only [classifyValues, encodePoint, encodeCode, ClassicalAlgorithms.EllipticCurve.encode,
    CShape.Value.ellipticCurvePointInfinityTag, CShape.Value.ellipticCurvePointX,
    CShape.Value.ellipticCurvePointY, Bool.false_eq_true, if_false,
    coordinateWord_eq_iff, coordinateWord_zero_iff]

private theorem additionOutputValue_encoded_represents (spec : CurveSpec width)
    (P Q : Pure.Point spec) :
    PointRepresents spec (additionOutputValue spec (encodePoint spec P) (encodePoint spec Q))
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec P Q) := by
  cases P with
  | zero =>
    change PointRepresents spec (encodePoint spec Q)
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec 0 Q)
    rw [ClassicalAlgorithms.EllipticCurve.Add.eval_left_infinity]
    exact encodePoint_represents spec Q
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change PointRepresents spec (encodePoint spec (.some x₁ y₁ h₁))
        (ClassicalAlgorithms.EllipticCurve.Add.eval spec (.some x₁ y₁ h₁) 0)
      rw [ClassicalAlgorithms.EllipticCurve.Add.eval_right_infinity]
      exact encodePoint_represents spec (.some x₁ y₁ h₁)
    | some x₂ y₂ h₂ =>
      rw [additionOutputValue, classifyValues_encoded_finite]
      by_cases sameX : x₁ = x₂
      · subst x₂
        rw [if_pos rfl]
        by_cases sameY : y₁ = y₂
        · subst y₂
          rw [if_pos rfl]
          by_cases zeroY : y₁ = 0
          · subst y₁
            rw [if_pos rfl]
            change PointRepresents spec (.ellipticCurvePoint true 0 0)
              (ClassicalAlgorithms.EllipticCurve.Double.eval spec (.some x₁ 0 h₁))
            rw [double_eval_eq_infinity_of_y_eq_zero]
            exact encodePoint_represents spec 0
          · rw [if_neg zeroY]
            have notInverse : (.some x₁ y₁ h₁ : Pure.Point spec) ≠ -(.some x₁ y₁ h₁) := by
              intro inverse
              rw [WeierstrassCurve.Affine.Point.neg_some] at inverse
              exact y_ne_mathlib_negY_of_ne_zero spec x₁ y₁ zeroY
                (WeierstrassCurve.Affine.Point.some.inj inverse).2
            have selected := ClassicalAlgorithms.EllipticCurve.Add.branch_doubling spec
              (.some x₁ y₁ h₁) (by simp) notInverse
            exact doublingOutputValue_represents_add_of_selected spec
              (CShape.unpackEllipticCurvePoint width (encodePoint spec (.some x₁ y₁ h₁)))
              x₁ y₁ h₁ rfl rfl selected
        · rw [if_neg sameY]
          have inverse : (.some x₁ y₁ h₁ : Pure.Point spec) = -(.some x₁ y₂ h₂) := by
            rcases (WeierstrassCurve.Affine.Point.X_eq_iff
              (W := spec.curve.toWeierstrassCurve.toAffine)).mp rfl with equal | inverse
            · exact False.elim (sameY (WeierstrassCurve.Affine.Point.some.inj equal).2)
            · exact inverse
          change PointRepresents spec (.ellipticCurvePoint true 0 0)
            (ClassicalAlgorithms.EllipticCurve.Add.eval spec (.some x₁ y₁ h₁) (.some x₁ y₂ h₂))
          rw [ClassicalAlgorithms.EllipticCurve.Add.eval, inverse, neg_add_cancel]
          exact encodePoint_represents spec 0
      · rw [if_neg sameX]
        have distinct : (.some x₁ y₁ h₁ : Pure.Point spec) ≠ (.some x₂ y₂ h₂) := by
          intro equal
          exact sameX (WeierstrassCurve.Affine.Point.some.inj equal).1
        have notInverse : (.some x₁ y₁ h₁ : Pure.Point spec) ≠ -(.some x₂ y₂ h₂) := by
          intro inverse
          exact sameX ((WeierstrassCurve.Affine.Point.X_eq_iff
            (W := spec.curve.toWeierstrassCurve.toAffine)).mpr (Or.inr inverse))
        have selected := ClassicalAlgorithms.EllipticCurve.Add.branch_generic spec
          (.some x₁ y₁ h₁) (.some x₂ y₂ h₂) (by simp) (by simp) notInverse distinct
        exact genericOutputValue_represents_add_of_selected spec
          (CShape.unpackEllipticCurvePoint width (encodePoint spec (.some x₁ y₁ h₁)))
          (CShape.unpackEllipticCurvePoint width (encodePoint spec (.some x₂ y₂ h₂)))
          x₁ x₂ y₁ y₂ h₁ h₂ rfl rfl rfl rfl selected

/-- The actual complete result represents the original sum on all represented input points. -/
theorem additionOutputValue_represents (spec : CurveSpec width)
    (left right : CShape.Value (PointShape width)) (P Q : Pure.Point spec)
    (leftRep : PointRepresents spec left P) (rightRep : PointRepresents spec right Q) :
    PointRepresents spec (additionOutputValue spec left right)
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec P Q) := by
  have leftCanonical : left = encodePoint spec P := by
    have encoded := ClassicalAlgorithms.EllipticCurve.encode_eq_of_decode_eq_some
      spec (decodeCode left) P leftRep
    exact (encodeCode_decodeCode left).symm.trans (congrArg encodeCode encoded.symm)
  have rightCanonical : right = encodePoint spec Q := by
    have encoded := ClassicalAlgorithms.EllipticCurve.encode_eq_of_decode_eq_some
      spec (decodeCode right) Q rightRep
    exact (encodeCode_decodeCode right).symm.trans (congrArg encodeCode encoded.symm)
  rw [leftCanonical, rightCanonical]
  exact additionOutputValue_encoded_represents spec P Q

/-- The same actual complete-addition record writes the original sum into the caller result cell. -/
theorem addIntoStep_represents {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (left right : CInputRef ctx (PointShape width)) (output : CWriteRef ctx (PointShape width))
    (store : Store ctx) (hidden : model.HiddenState) (P Q : Pure.Point spec)
    (leftRep : PointRepresents spec (store.read left) P)
    (rightRep : PointRepresents spec (store.read right) Q) :
    PointRepresents spec ((addIntoStep spec left right output (store, hidden)).1.1.read
      (classifierRead output))
      (ClassicalAlgorithms.EllipticCurve.Add.eval spec P Q) := by
  rw [addIntoStep_store]
  simpa only [classifierRead, Store.read_write_same] using
    additionOutputValue_represents spec (store.read left) (store.read right) P Q leftRep rightRep

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
