/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Engine.Model

/-!
# Original optional recovery output from actual selected words

The pure encoding below describes the original candidate and independent
reconstruction flag. Actual normalized multiplication and reconstruction
produce that full encoding when their stored words are the original residues.
The checked unit decision then selects exactly the original optional result.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalAlgorithms.Modular Modular.NativePower NormalizedRecovery.Native

noncomputable section

variable {width : Nat}

/-- Fixed public encoding of the original candidate and its reconstruction flag. -/
def encodedRecoveryOutput (spec : ModulusSpec width) (output : FiniteCyclicDLP.Output spec) :
    CShape.Value (FiniteCyclicDLP.OutputShape width) :=
  .product (CShape.wordOfNat width output.candidate.val) (.bit output.verified)

/-- Fixed optional encoding of the original mathematical raw-recovery result. -/
def encodedRawOutput (spec : ModulusSpec width) (output : Option (FiniteCyclicDLP.Output spec)) :
    CShape.Value (OutputShape width) :=
  match output with
  | none => .optionNone
  | some value => .optionSome (encodedRecoveryOutput spec value)

private lemma word_eq_of_toNat (word : CShape.Word width) (value : Nat)
    (fits : value < 2 ^ width) (same : word.toNat = value) :
    word = CShape.wordOfNat width value := by
  cases word with
  | unsignedWord bits =>
    apply congrArg CShape.Value.unsignedWord
    apply Fin.ext
    change bits.val = value % 2 ^ width
    rw [Nat.mod_eq_of_lt fits]
    exact same

/-- Actual full-word multiplication and reconstruction produce the complete original output. -/
lemma recoveryValue_original (spec : ModulusSpec width) (semantic : FiniteCyclicDLP.Input spec)
    (left right inverse : CShape.Word width) (modulus : CShape.Word (width + 1))
    (modulusValue : modulus.toNat = spec.modulus)
    (leftValue : left.toNat = semantic.leftFrequency.val)
    (rightValue : right.toNat = semantic.negatedRightFrequency.val)
    (inverseValue : inverse.toNat = semantic.leftInverse.val) :
    recoveryValue left right inverse modulus =
      encodedRecoveryOutput spec (FiniteCyclicDLP.outputOf spec semantic) := by
  have positive : 0 < modulus.toNat := by rw [modulusValue]; exact modulusSpec_modulus_pos spec
  have fits : modulus.toNat ≤ 2 ^ width := by rw [modulusValue]; exact spec.le_capacity
  have candidateValue := nativePower_multiplyValue_toNat right inverse modulus positive fits
  have reconstructionValue := nativePower_multiplyValue_toNat
    (multiplyValue right inverse modulus) left modulus positive fits
  have candidateNat : (multiplyValue right inverse modulus).toNat =
      (FiniteCyclicDLP.outputOf spec semantic).candidate.val := by
    rw [candidateValue, rightValue, inverseValue, modulusValue]
    rfl
  have candidate := word_eq_of_toNat (multiplyValue right inverse modulus)
    (FiniteCyclicDLP.outputOf spec semantic).candidate.val
    ((FiniteCyclicDLP.outputOf spec semantic).candidate.isLt.trans_le spec.le_capacity) candidateNat
  have verified : decide ((multiplyValue (multiplyValue right inverse modulus) left modulus).toNat =
      right.toNat) = (FiniteCyclicDLP.outputOf spec semantic).verified := by
    rw [reconstructionValue, candidateNat, leftValue, rightValue, modulusValue]
    rfl
  exact congrArg₂ CShape.Value.product candidate (congrArg CShape.Value.bit verified)

/-- Original stored unit decision and original successful inverse give exactly `outputOf`. -/
lemma selectedRecoveryValue_original (spec : ModulusSpec width)
    (original : CShape.Value (InputShape width)) (success : CShape.Value .bit)
    (left right inverse : CShape.Word width) (modulus : CShape.Word (width + 1))
    (modulusValue : modulus.toNat = spec.modulus)
    (leftValue : left.toNat = (normalize spec original).left.val)
    (rightValue : right.toNat = (negateRight spec (normalize spec original)).val)
    (statusValue : success = .bit (NumberTheory.Checked.Engine.unitDecision spec
      (normalize spec original).left))
    (inverseValue : NumberTheory.Checked.Engine.unitDecision spec
        (normalize spec original).left = true → inverse.toNat =
          (NumberTheory.Checked.Engine.inverseCoefficient spec
            (normalize spec original).left).val) :
    (if success.toBool then .optionSome (recoveryValue left right inverse modulus)
      else .optionNone) = encodedRawOutput spec (RawRecovery.outputOf spec original) := by
  let normalized := normalize spec original
  have checked := NumberTheory.Checked.Engine.checkedEngine_checkedInverse_eq_tryInvEval
    spec normalized.left
  unfold RawRecovery.outputOf
  dsimp only
  rw [← checked]
  by_cases unit : NumberTheory.Checked.Engine.unitDecision spec normalized.left = true
  · rw [NumberTheory.Checked.Engine.checkedEngine_checkedInverse_of_unitDecision_true
      spec normalized.left unit]
    have chosen : success.toBool = true := by rw [statusValue, unit]; rfl
    simp only [chosen, if_true, encodedRawOutput]
    apply congrArg CShape.Value.optionSome
    exact recoveryValue_original spec
      (helperInput spec normalized (NumberTheory.Checked.Engine.inverseCoefficient
        spec normalized.left)) left right inverse modulus modulusValue leftValue rightValue
      (inverseValue unit)
  · have rejected : NumberTheory.Checked.Engine.unitDecision spec normalized.left = false :=
      Bool.eq_false_iff.mpr unit
    rw [NumberTheory.Checked.Engine.checkedEngine_checkedInverse_of_unitDecision_false
      spec normalized.left rejected]
    have chosen : success.toBool = false := by rw [statusValue, rejected]; rfl
    simp only [chosen, Bool.false_eq_true, if_false, encodedRawOutput]

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
