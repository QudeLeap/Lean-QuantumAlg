/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Nearest.Model
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Checked

/-!
# Actual checked exposure for arbitrary canonical normalized inputs

The actual checked inverse, native multiplication, reconstruction and three
caller writes consume canonical residues directly.  This interface applies
the existing actual checked circuit to the nearest decoder's normalized words
without assuming that they arose from truncated-range rescaling.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular NormalizedRecovery.Native
open RawRecovery.Native

noncomputable section

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {width : Nat}

/-- Original stored unit decision and original successful inverse give exactly `outputOf`. -/
lemma selectedRecoveryValue_normalized (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec) (success : CShape.Value .bit)
    (left right inverse : CShape.Word width) (modulus : CShape.Word (width + 1))
    (modulusValue : modulus.toNat = spec.modulus)
    (leftValue : left.toNat = normalized.left.val)
    (rightValue : right.toNat = (negateRight spec normalized).val)
    (statusValue : success = .bit (NumberTheory.Checked.Engine.unitDecision spec
      normalized.left))
    (inverseValue : NumberTheory.Checked.Engine.unitDecision spec
        normalized.left = true → inverse.toNat =
          (NumberTheory.Checked.Engine.inverseCoefficient spec
            normalized.left).val) :
    (if success.toBool then .optionSome (recoveryValue left right inverse modulus)
      else .optionNone) = encodedRawOutput spec (outputOfNormalized spec normalized) := by
  have checked := NumberTheory.Checked.Engine.checkedEngine_checkedInverse_eq_tryInvEval
    spec normalized.left
  unfold outputOfNormalized
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

/-- The original checked decision and selected payload give all three original public values. -/
lemma exposedRecoveryValue_normalized (spec : ModulusSpec width)
    (normalized : RawRecovery.NormalizedInput spec) (success : CShape.Value .bit)
    (left right inverse : CShape.Word width) (modulus : CShape.Word (width + 1))
    (modulusValue : modulus.toNat = spec.modulus)
    (leftValue : left.toNat = normalized.left.val)
    (rightValue : right.toNat = (negateRight spec normalized).val)
    (statusValue : success = .bit (NumberTheory.Checked.Engine.unitDecision spec
      normalized.left))
    (inverseValue : NumberTheory.Checked.Engine.unitDecision spec
        normalized.left = true → inverse.toNat =
          (NumberTheory.Checked.Engine.inverseCoefficient spec
            normalized.left).val) :
    .product success (if success.toBool then recoveryValue left right inverse modulus
      else CShape.initialValue (FiniteCyclicDLP.OutputShape width)) =
        outputCellsNormalized spec normalized := by
  have encoded := selectedRecoveryValue_normalized spec normalized success left right inverse
    modulus modulusValue leftValue rightValue statusValue inverseValue
  cases success with
  | bit selected =>
    cases selected with
    | false =>
      cases outcome : outputOfNormalized spec normalized with
      | none =>
        rw [outputCellsNormalized_of_none spec normalized outcome]
        rfl
      | some output =>
        simp only [CShape.Value.toBool, Bool.false_eq_true, if_false, outcome,
          encodedRawOutput] at encoded
        cases encoded
    | true =>
      cases outcome : outputOfNormalized spec normalized with
      | none =>
        simp only [CShape.Value.toBool, if_true, outcome, encodedRawOutput] at encoded
        cases encoded
      | some output =>
        have same : recoveryValue left right inverse modulus =
            encodedRecoveryOutput spec output := by
          simpa only [CShape.Value.toBool, if_true, outcome, encodedRawOutput,
            CShape.Value.optionSome.injEq] using encoded
        rw [outputCellsNormalized_of_some spec normalized output outcome]
        exact congrArg
          (fun payload : CShape.Value (FiniteCyclicDLP.OutputShape width) =>
            CShape.Value.product (.bit true) payload) same

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}

/-- The actual checked store supplies the three copied values and their original interpretation. -/
lemma checkedExposureBody_normalized_record (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit)
    (successLeft : success.key ∉ left.storageKeys)
    (inverseLeft : inverse.key ∉ left.storageKeys)
    (successRight : success.key ∉ negatedRight.storageKeys)
    (inverseRight : inverse.key ∉ negatedRight.storageKeys)
    (successModulus : success.key ∉ modulus.storageKeys)
    (inverseModulus : inverse.key ∉ modulus.storageKeys) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (checkedExposureBody (model := model) spec left negatedRight modulus
        success inverse inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (checkedExposureBody (model := model) spec left negatedRight modulus success inverse
          inverseSuccess
          candidate reconstruction).execute
            environment Reference state = state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, ∃ checked : Store ctx,
        ∃ value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape width)),
          (∀ {shape : CShape} (other : CInputRef ctx shape),
            success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
              checked.read other = before.1.read other) ∧
          (record before).1.1 = exposureWrite inverseSuccess candidate reconstruction checked
            value ∧
          ∀ normalized : RawRecovery.NormalizedInput spec,
            (before.1.read modulus).toNat = spec.modulus →
            (before.1.read left).toNat = normalized.left.val →
            (before.1.read negatedRight).toNat = (negateRight spec normalized).val →
            value = outputCellsNormalized spec normalized := by
  obtain ⟨checkedRecord, checkedEquation, checkedCorrect⟩ :=
    NumberTheory.Checked.Native.withCheckedInverse_actualRecord (model := model) spec left success
      inverse
  let recoveryInput := CInputRef.product left (.product negatedRight (scaleRead inverse))
  obtain ⟨selectedRecord, selectedEquation, selectedCorrect⟩ :=
    withSelectedExposure_actualRecord (model := model) recoveryInput modulus (scaleRead success)
      inverseSuccess candidate reconstruction
  let first := NumberTheory.Checked.Native.withCheckedInverse (model := model)
    spec left success inverse
  let second := withSelectedExposure (model := model) recoveryInput modulus (scaleRead success)
    inverseSuccess candidate reconstruction
  refine ⟨Circuit.sequenceRecord first second checkedRecord selectedRecord,
    Circuit.execute_sequenceRecord
      (environment := environment) first second checkedRecord selectedRecord
      checkedEquation selectedEquation, ?_⟩
  intro before
  let checked := (checkedRecord before).1.1
  refine ⟨checked, .product (checked.read (scaleRead success))
    (if (checked.read (scaleRead success)).toBool then
      recoveryValue (checked.read left) (checked.read negatedRight)
        (checked.read (scaleRead inverse)) (checked.read modulus)
      else CShape.initialValue (FiniteCyclicDLP.OutputShape width)),
    (checkedCorrect before).1, selectedCorrect (checkedRecord before).1, ?_⟩
  intro normalized modulusValue leftValue rightValue
  have leftRead : checked.read left = before.1.read left :=
    (checkedCorrect before).1 left successLeft inverseLeft
  have rightRead : checked.read negatedRight = before.1.read negatedRight :=
    (checkedCorrect before).1 negatedRight successRight inverseRight
  have modulusRead : checked.read modulus = before.1.read modulus :=
    (checkedCorrect before).1 modulus successModulus inverseModulus
  have actual := (checkedCorrect before).2 normalized.left leftValue
  exact exposedRecoveryValue_normalized spec normalized (checked.read (scaleRead success))
    (checked.read left) (checked.read negatedRight) (checked.read (scaleRead inverse))
    (checked.read modulus) ((congrArg CShape.Value.toNat modulusRead).trans modulusValue)
    ((congrArg CShape.Value.toNat leftRead).trans leftValue)
    ((congrArg CShape.Value.toNat rightRead).trans rightValue) actual.1 actual.2.1

/-- Real checked-output allocation leaves exactly the original three chronological caller writes. -/
lemma withCheckedExposure_normalized_record (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (withCheckedExposure (model := model) spec refs inverseSuccess candidate
          reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (withCheckedExposure (model := model) spec refs inverseSuccess candidate
          reconstruction).execute
          environment Reference state = state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          inverseSuccess.key ∉ other.storageKeys → candidate.key ∉ other.storageKeys →
            reconstruction.key ∉ other.storageKeys →
              (record before).1.1.read other = before.1.read other) ∧
        ∀ normalized : RawRecovery.NormalizedInput spec,
          (before.1.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
          (before.1.read (scaleRead refs.left)).toNat = normalized.left.val →
          (before.1.read (scaleRead refs.negatedRight)).toNat =
            (negateRight spec normalized).val →
          (record before).1.1 = exposureWrite inverseSuccess candidate reconstruction before.1
            (outputCellsNormalized spec normalized) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      inverseSuccess.key ∉ other.storageKeys → candidate.key ∉ other.storageKeys →
        reconstruction.key ∉ other.storageKeys → after.read other = before.read other) ∧
    ∀ normalized : RawRecovery.NormalizedInput spec,
      (before.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
      (before.read (scaleRead refs.left)).toNat = normalized.left.val →
      (before.read (scaleRead refs.negatedRight)).toNat =
        (negateRight spec normalized).val →
      after = exposureWrite inverseSuccess candidate reconstruction before
        (outputCellsNormalized spec normalized)
  unfold withCheckedExposure
  apply withCells_actualRecord_initialized_restricted_post (environment := environment) _ _ _ Post
  intro inner cells _distinct transport separated
  have free : ∀ {shape : CShape} (input : CInputRef ctx shape),
      (checkedSuccessCell cells).key ∉ (transport.liftInput input).storageKeys ∧
        (checkedInverseCell cells).key ∉ (transport.liftInput input).storageKeys := by
    intro shape input
    cases cells with
    | cons inverse rest =>
      cases rest with
      | cons success rest =>
        cases rest
        exact ⟨separated.2.1 input, separated.1 input⟩
  obtain ⟨record, equation, correct⟩ := checkedExposureBody_normalized_record (model := model) spec
    (transport.liftInput (scaleRead refs.left))
    (transport.liftInput (scaleRead refs.negatedRight))
    (transport.liftInput (scaleRead refs.modulusWide))
    (checkedSuccessCell cells) (checkedInverseCell cells)
    (transport.liftWrite inverseSuccess) (transport.liftWrite candidate)
    (transport.liftWrite reconstruction)
    (free (scaleRead refs.left)).1 (free (scaleRead refs.left)).2
    (free (scaleRead refs.negatedRight)).1 (free (scaleRead refs.negatedRight)).2
    (free (scaleRead refs.modulusWide)).1 (free (scaleRead refs.modulusWide)).2
  refine ⟨record, equation, ?_⟩
  intro before _initialized
  obtain ⟨checked, value, checkedFrame, written, interpreted⟩ := correct before
  have entered : transport.ReadsAs (transport.restrict before.1) before.1 :=
    transport.workspaceTransport_restrict_readsAs before.1
  have checkedReads : transport.ReadsAs (transport.restrict before.1) checked := by
    intro shape other
    exact (checkedFrame (transport.liftInput other) (free other).1 (free other).2).trans
      (entered other)
  have finalReads : transport.ReadsAs
      (exposureWrite inverseSuccess candidate reconstruction (transport.restrict before.1) value)
      (record before).1.1 := by
    rw [written]
    intro shape other
    exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction
      (transport.restrict before.1) checked checkedReads value other
  have exactStore := (transport.workspaceTransport_readsAs_restrict_iff).mp finalReads
  constructor
  · intro shape other successFree candidateFree reconstructionFree
    rw [exactStore]
    exact exposureWrite_read_other inverseSuccess candidate reconstruction
      (transport.restrict before.1) value other successFree candidateFree reconstructionFree
  · intro normalized modulusValue leftValue rightValue
    have actual := interpreted normalized
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.modulusWide))).trans modulusValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.left))).trans leftValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.negatedRight))).trans rightValue)
    exact exactStore.trans (congrArg
      (exposureWrite inverseSuccess candidate reconstruction (transport.restrict before.1)) actual)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
