/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-!
# Unit duration of the original independent attempt allowance

The original duration definitions and native pools follow the same serial
stages and conditional branches. Unit duration sums are bounded by those
same pool cardinalities; the result is not inferred from the cost of a
particular execution path. Every loader and both checked flags remain charged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open NumberTheory.XGCD.Native NumberTheory.Checked.Native
open NumberTheory.Checked.SignedReduction.Native
open FiniteCyclicDLP.RawRecovery.Native Field.Native Add.Native

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {width scalarWidth : Nat}

private lemma list_unit {α : Type} (events : List α) :
    (events.map (fun _ => (1 : Nat))).sum = events.length := by simp

omit [BitWord.Selected model] in
private lemma max_card (left right : ResourcePool model) :
    max left.card right.card ≤ (ResourcePool.max left right).card :=
  max_le (Multiset.card_le_card (ResourcePool.le_max_left left right))
    (Multiset.card_le_card (ResourcePool.le_max_right left right))

omit [BitWord.Selected model] in
private lemma combine_card {left right : Nat} (first second : ResourcePool model)
    (firstBound : left ≤ first.card) (secondBound : right ≤ second.card) :
    max left right ≤ (ResourcePool.max first second).card :=
  (max_le_max firstBound secondBound).trans (max_card first second)

private lemma raw_unit (width : Nat) :
    rawDepthLimit width (fun _ : Resource.Event model => 1) =
      (rawEnvelope model width).card :=
  (xgcdNativeRawDepthLimit_unit model width).trans (rawEnvelope_card model width).symm

private lemma signed_unit (width : Nat) :
    signedReductionDepthLimit width (fun _ : Resource.Event model => 1) ≤
      (signedReductionEnvelope model width).card := by
  have magnitude := max_card
    (ResourcePool.ofList (signedMagnitudeEvents model width true))
    (ResourcePool.ofList (signedMagnitudeEvents model width false))
  have correction := max_card
    (ResourcePool.ofList (finalCorrectionEvents model width true))
    (ResourcePool.ofList (finalCorrectionEvents model width false))
  simp only [ResourcePool.ofList, Multiset.coe_card] at magnitude correction
  simp only [signedReductionDepthLimit, signedReductionEnvelope, list_unit,
    Multiset.card_add, ResourcePool.ofList, Multiset.coe_card]
  omega

private lemma coefficient_unit (spec : ModulusSpec width) :
    coefficientDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (coefficientEnvelope model spec).card := by
  have raw := raw_unit (model := model) (width + 1)
  have signed := signed_unit (model := model) width
  simp only [coefficientDepthLimit, coefficientEnvelope, list_unit, Multiset.card_add,
    ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil]
  omega

private lemma affine_unit (spec : ModulusSpec width) :
    affineDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (affineEnvelope model spec).card := by
  have coefficient := coefficient_unit (model := model) spec
  simp only [affineDepthLimit, affineStageDepthLimit, affineEnvelope, affineStageEnvelope,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero,
    add_zero, Multiset.card_add, list_unit, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

private lemma generic_unit (spec : ModulusSpec width) :
    genericDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (genericEnvelope model spec).card := by
  have affine := affine_unit (model := model) spec
  simp only [genericDepthLimit, genericEnvelope, list_unit, Multiset.card_add,
    ResourcePool.ofList, Multiset.coe_card]
  omega

private lemma doubling_unit (spec : CurveSpec width) :
    doublingDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (doublingEnvelope model spec).card := by
  have affine := affine_unit (model := model) spec.field
  simp only [doublingDepthLimit, doublingStageDepthLimit, doublingEnvelope,
    doublingStageEnvelope, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero, Multiset.card_add, list_unit,
    ResourcePool.ofList, Multiset.coe_card]
  omega

private lemma addition_arm_unit (spec : CurveSpec width) (selected : Case) :
    additionArmDepthLimit spec (fun _ : Resource.Event model => 1) selected ≤
      (additionArmEnvelope model spec selected).card := by
  cases selected with
  | generic => exact generic_unit spec.field
  | doubling => exact doubling_unit spec
  | vertical => exact Nat.le_refl _
  | leftInfinity => exact Nat.le_refl _
  | rightInfinity => exact Nat.le_refl _

private lemma addition_unit (spec : CurveSpec width) :
    additionDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (additionEnvelope model spec).card := by
  have branch : caseMaximum Nat.max
      (additionArmDepthLimit spec (fun _ : Resource.Event model => 1)) ≤
        (additionBranchEnvelope model spec).card := by
    unfold additionBranchEnvelope caseMaximum
    exact combine_card _ _ (addition_arm_unit spec .leftInfinity)
      (combine_card _ _ (addition_arm_unit spec .rightInfinity)
        (combine_card _ _
          (combine_card _ _
            (combine_card _ _ (addition_arm_unit spec .vertical)
              (addition_arm_unit spec .doubling))
            (addition_arm_unit spec .vertical))
          (addition_arm_unit spec .generic)))
  simp only [additionDepthLimit, additionEnvelope, list_unit, Multiset.card_add,
    ResourcePool.ofList, Multiset.coe_card]
  exact Nat.add_le_add_left branch _

private lemma scalar_unit (spec : CurveSpec width) (count : Nat) :
    ScalarMul.Native.scalarDepthLimit spec count (fun _ : Resource.Event model => 1) ≤
      (ScalarMul.Native.scalarEnvelope model spec count).card := by
  have addition := addition_unit (model := model) spec
  simp only [ScalarMul.Native.scalarDepthLimit, ScalarMul.Native.scalarEnvelope,
    list_unit, Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul,
    ResourcePool.ofList, Multiset.coe_card]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left count (Nat.add_le_add addition addition)) _

private lemma verification_unit (spec : CurveSpec width) (count : Nat) :
    verificationDepthLimit spec count (fun _ : Resource.Event model => 1) ≤
      (verificationEnvelope model spec count).card := by
  have scalar := scalar_unit (model := model) spec count
  simp only [verificationDepthLimit, verificationStageDepthLimit, verificationEnvelope,
    verificationStageEnvelope, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, Multiset.card_add,
    list_unit, PointEquality.coreEnvelope, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

private lemma checked_unit (spec : ModulusSpec width) :
    checkedInverseDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (checkedInverseEnvelope model spec).card := by
  have raw := raw_unit (model := model) (width + 1)
  have signed := signed_unit (model := model) width
  simp only [checkedInverseDepthLimit, checkedInverseEnvelope, checkedSelectionDepthLimit,
    checkedSelectionEnvelope, ResourcePool.max, Multiset.union_zero, list_unit,
    Multiset.card_add, ResourcePool.ofList, Multiset.coe_card,
    checkedDecisionEvents, List.length_cons, List.length_nil]
  omega

private lemma preparation_unit (spec : ModulusSpec width) :
    preparationDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (preparationEnvelope model spec).card := by
  have selected := Multiset.card_le_card (ResourcePool.le_max_left
    (ResourcePool.ofList (negateEvents model width true))
    (ResourcePool.ofList (negateEvents model width false)))
  change 2 ≤ (ResourcePool.max _ _).card at selected
  simp only [ResourcePool.ofList] at selected
  simp only [preparationDepthLimit, preparationEnvelope, preparationFinalEnvelope,
    measuredDecodeEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    ResourcePool.scale, ResourcePool.singleton, Multiset.card_add, Multiset.card_nsmul,
    Multiset.card_replicate, list_unit, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil]
  omega

private lemma selected_unit (width : Nat) :
    selectedExposureDepthLimit width (fun _ : Resource.Event model => 1) =
      (ResourcePool.ofList (selectedExposureEvents model width true)).card := rfl

private lemma exposure_unit (spec : ModulusSpec width) :
    singleExposureDepthLimit spec (fun _ : Resource.Event model => 1) ≤
      (singleExposureEnvelope model spec).card := by
  have preparation := preparation_unit (model := model) spec
  have checked := checked_unit (model := model) spec
  have selected := selected_unit (model := model) width
  simp only [singleExposureDepthLimit, checkedExposureDepthLimit, singleExposureEnvelope,
    checkedExposureEnvelope, Multiset.card_add]
  omega

/-- Unit durations of the original attempt allowance are bounded by that same native pool. -/
lemma attemptDepthLimit_unit_le_card (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth) :
    attemptDepthLimit curve modulus (fun _ : Resource.Event model => 1) ≤
      (attemptEnvelope model curve modulus).card := by
  have exposure := exposure_unit (model := model) modulus
  have verification := verification_unit (model := model) curve scalarWidth
  simp only [attemptDepthLimit, attemptEnvelope, FirstAccepted.nativeEnvelope,
    List.map_append, List.sum_append, list_unit, Multiset.card_add,
    ResourcePool.ofList, Multiset.coe_card]
  omega

/-- The complete serial unit-duration allowance retains the original numerical ceiling. -/
lemma attemptDepthLimit_unit_le (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth) :
    attemptDepthLimit curve modulus (fun _ : Resource.Event model => 1) ≤
      42 * scalarWidth + scalarWidth * (248 * width + 644) + 119 :=
  (attemptDepthLimit_unit_le_card curve modulus).trans (attemptEnvelope_card_le model curve modulus)

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
