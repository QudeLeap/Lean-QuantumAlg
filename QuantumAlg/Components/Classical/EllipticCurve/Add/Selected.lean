/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model
import all QuantumAlg.Util.Classical.EllipticCurve.Formulas

/-!
# Original selected finite point-addition conditions

The original generic and doubling branch decisions imply their affine
exclusions and unit denominators. These pure statements retain their names
and bodies independently of the executable point-addition backend. The
runtime computation receives no supplied inverse or unit proof.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add

open ClassicalAlgorithms
open ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve

noncomputable section

private theorem generic_conditions_of_selected {width : Nat}
    (spec : CurveSpec width) (left right : Pure.Point spec)
    (selected :
      ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
        .generic) :
    left ≠ 0 ∧ right ≠ 0 ∧ left ≠ -right ∧ left ≠ right := by
  have leftNonzero : left ≠ 0 := by
    intro leftZero
    have selectedLeft :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .leftInfinity := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_pos leftZero]
    rw [selectedLeft] at selected
    cases selected
  have rightNonzero : right ≠ 0 := by
    intro rightZero
    have selectedRight :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .rightInfinity := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_pos rightZero]
    rw [selectedRight] at selected
    cases selected
  have notInverse : left ≠ -right := by
    intro inverse
    have selectedInverse :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .inverseOrVertical := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_neg rightNonzero, if_pos inverse]
    rw [selectedInverse] at selected
    cases selected
  have distinct : left ≠ right := by
    intro equal
    have selectedDoubling :
      ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .doubling := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_neg rightNonzero, if_neg notInverse, if_pos equal]
    rw [selectedDoubling] at selected
    cases selected
  exact ⟨leftNonzero, rightNonzero, notInverse, distinct⟩

private theorem doubling_conditions_of_selected {width : Nat}
    (spec : CurveSpec width) (left right : Pure.Point spec)
    (selected :
      ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
        .doubling) :
    left ≠ 0 ∧ right ≠ 0 ∧ left ≠ -right ∧ left = right := by
  have leftNonzero : left ≠ 0 := by
    intro leftZero
    have selectedLeft :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .leftInfinity := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_pos leftZero]
    rw [selectedLeft] at selected
    cases selected
  have rightNonzero : right ≠ 0 := by
    intro rightZero
    have selectedRight :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .rightInfinity := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_pos rightZero]
    rw [selectedRight] at selected
    cases selected
  have notInverse : left ≠ -right := by
    intro inverse
    have selectedInverse :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .inverseOrVertical := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_neg rightNonzero, if_pos inverse]
    rw [selectedInverse] at selected
    cases selected
  have equal : left = right := by
    by_contra distinct
    have selectedGeneric :
        ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
          .generic := by
      simp only [ClassicalAlgorithms.EllipticCurve.Add.branch,
        if_neg leftNonzero, if_neg rightNonzero, if_neg notInverse,
        if_neg distinct]
    rw [selectedGeneric] at selected
    cases selected
  exact ⟨leftNonzero, rightNonzero, notInverse, equal⟩

/-- A selected generic finite branch gives a unit secant denominator.  The
proof passes through the affine point facts, rather than treating an arbitrary
raw coefficient as an inverse. -/
theorem generic_denominator_isUnit_of_selected {width : Nat}
    (spec : CurveSpec width)
    (left right : Pure.Point spec)
    (x₁ x₂ y₁ y₂ : ZMod spec.field.modulus)
    (h₁ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₁ y₁)
    (h₂ : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x₂ y₂)
    (leftFinite : left = (.some x₁ y₁ h₁ : Pure.Point spec))
    (rightFinite : right = (.some x₂ y₂ h₂ : Pure.Point spec))
    (selected :
      ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
        .generic) :
    IsUnit
      (ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.genericAddDenominator
        spec x₁ x₂) := by
  have conditions := generic_conditions_of_selected spec left right selected
  have distinct := conditions.2.2.2
  have notInverse := conditions.2.2.1
  rw [leftFinite, rightFinite] at distinct notInverse
  have xDistinct :=
    ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.genericFinite_x_ne
      spec x₁ x₂ y₁ y₂ h₁ h₂ distinct notInverse
  exact
    ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.genericAddDenominator_isUnit
      spec xDistinct

/-- A selected finite doubling branch gives a unit tangent denominator. -/
theorem doubling_denominator_isUnit_of_selected {width : Nat}
    (spec : CurveSpec width)
    (left right : Pure.Point spec)
    (x y : ZMod spec.field.modulus)
    (h : spec.curve.toWeierstrassCurve.toAffine.Nonsingular x y)
    (leftFinite : left = (.some x y h : Pure.Point spec))
    (rightFinite : right = (.some x y h : Pure.Point spec))
    (selected :
      ClassicalAlgorithms.EllipticCurve.Add.branch spec left right =
        .doubling) :
    IsUnit
      (ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.doubleDenominator
        spec y) := by
  have conditions := doubling_conditions_of_selected spec left right selected
  have notInverse := conditions.2.2.1
  rw [leftFinite, rightFinite] at notInverse
  have yNonzero :=
    ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.doubleFinite_y_ne_zero
      spec x y h notInverse
  exact
    ClassicalAlgorithms.EllipticCurve.ShortWeierstrass.doubleDenominator_isUnit
      spec y yNonzero

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add
