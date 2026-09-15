/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Selection
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Values
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Actual checked inversion and three-cell exposure

The existing checked circuit produces its own status and inverse. Its actual
returned store feeds the selected recovery and the three ordered copies. Two
real lexical cells remove all caller scratch and input-separation premises.
The final store records chronological writes even when caller outputs alias.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular NormalizedRecovery.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual checked store supplies the three copied values and their original interpretation. -/
theorem checkedExposureBody_actualRecord (spec : ModulusSpec width)
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
    ∃ record : Store ctx → Store ctx × (checkedExposureBody spec left negatedRight modulus
        success inverse inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (checkedExposureBody spec left negatedRight modulus success inverse inverseSuccess
          candidate reconstruction).execute Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx, ∃ checked : Store ctx,
        ∃ value : CShape.Value (.product .bit (FiniteCyclicDLP.OutputShape width)),
          (∀ {shape : CShape} (other : CInputRef ctx shape),
            success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
              checked.read other = before.read other) ∧
          (record before).1 = exposureWrite inverseSuccess candidate reconstruction checked value ∧
          ∀ original : CShape.Value (InputShape width),
            (before.read modulus).toNat = spec.modulus →
            (before.read left).toNat = (normalize spec original).left.val →
            (before.read negatedRight).toNat = (negateRight spec (normalize spec original)).val →
            value = RawRecovery.outputCells spec original := by
  obtain ⟨checkedRecord, checkedEquation, checkedCorrect⟩ :=
    NumberTheory.Checked.Native.withCheckedInverse_actualRecord spec left success inverse
  let recoveryInput := CInputRef.product left (.product negatedRight (scaleRead inverse))
  obtain ⟨selectedRecord, selectedEquation, selectedCorrect⟩ :=
    withSelectedExposure_actualRecord recoveryInput modulus (scaleRead success)
      inverseSuccess candidate reconstruction
  refine ⟨Circuit.sequenceRecord _ _ checkedRecord selectedRecord,
    Circuit.execute_sequenceRecord _ _ _ _ checkedEquation selectedEquation, ?_⟩
  intro before
  let checked := (checkedRecord before).1
  refine ⟨checked, .product (checked.read (scaleRead success))
    (if (checked.read (scaleRead success)).toBool then
      recoveryValue (checked.read left) (checked.read negatedRight)
        (checked.read (scaleRead inverse)) (checked.read modulus)
      else CShape.initialValue (FiniteCyclicDLP.OutputShape width)),
    (checkedCorrect before).1, selectedCorrect checked, ?_⟩
  intro original modulusValue leftValue rightValue
  have leftRead : checked.read left = before.read left :=
    (checkedCorrect before).1 left successLeft inverseLeft
  have rightRead : checked.read negatedRight = before.read negatedRight :=
    (checkedCorrect before).1 negatedRight successRight inverseRight
  have modulusRead : checked.read modulus = before.read modulus :=
    (checkedCorrect before).1 modulus successModulus inverseModulus
  have actual := (checkedCorrect before).2 (normalize spec original).left leftValue
  exact exposedRecoveryValue_original spec original (checked.read (scaleRead success))
    (checked.read left) (checked.read negatedRight) (checked.read (scaleRead inverse))
    (checked.read modulus) ((congrArg CShape.Value.toNat modulusRead).trans modulusValue)
    ((congrArg CShape.Value.toNat leftRead).trans leftValue)
    ((congrArg CShape.Value.toNat rightRead).trans rightValue) actual.1 actual.2.1

/-- Real checked-output allocation leaves exactly the original three chronological caller writes. -/
theorem withCheckedExposure_actualRecord (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width)
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord width))
    (reconstruction : CWriteRef ctx .bit) :
    ∃ record : Store ctx → Store ctx ×
        (withCheckedExposure spec refs inverseSuccess candidate reconstruction).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCheckedExposure spec refs inverseSuccess candidate reconstruction).execute
          Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          inverseSuccess.key ∉ other.storageKeys → candidate.key ∉ other.storageKeys →
            reconstruction.key ∉ other.storageKeys →
              (record before).1.read other = before.read other) ∧
        ∀ original : CShape.Value (InputShape width),
          (before.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
          (before.read (scaleRead refs.left)).toNat = (normalize spec original).left.val →
          (before.read (scaleRead refs.negatedRight)).toNat =
            (negateRight spec (normalize spec original)).val →
          (record before).1 = exposureWrite inverseSuccess candidate reconstruction before
            (RawRecovery.outputCells spec original) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape),
      inverseSuccess.key ∉ other.storageKeys → candidate.key ∉ other.storageKeys →
        reconstruction.key ∉ other.storageKeys → after.read other = before.read other) ∧
    ∀ original : CShape.Value (InputShape width),
      (before.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
      (before.read (scaleRead refs.left)).toNat = (normalize spec original).left.val →
      (before.read (scaleRead refs.negatedRight)).toNat =
        (negateRight spec (normalize spec original)).val →
      after = exposureWrite inverseSuccess candidate reconstruction before
        (RawRecovery.outputCells spec original)
  unfold withCheckedExposure
  apply withCells_actualRecord_initialized_restricted_post _ _ _ Post
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
  obtain ⟨record, equation, correct⟩ := checkedExposureBody_actualRecord spec
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
  have entered : transport.ReadsAs (transport.restrict before) before :=
    transport.workspaceTransport_restrict_readsAs before
  have checkedReads : transport.ReadsAs (transport.restrict before) checked := by
    intro shape other
    exact (checkedFrame (transport.liftInput other) (free other).1 (free other).2).trans
      (entered other)
  have finalReads : transport.ReadsAs
      (exposureWrite inverseSuccess candidate reconstruction (transport.restrict before) value)
      (record before).1 := by
    rw [written]
    intro shape other
    exact exposureWrite_readsAs transport inverseSuccess candidate reconstruction
      (transport.restrict before) checked checkedReads value other
  have exactStore := (transport.workspaceTransport_readsAs_restrict_iff).mp finalReads
  constructor
  · intro shape other successFree candidateFree reconstructionFree
    rw [exactStore]
    exact exposureWrite_read_other inverseSuccess candidate reconstruction
      (transport.restrict before) value other successFree candidateFree reconstructionFree
  · intro original modulusValue leftValue rightValue
    have actual := interpreted original
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.modulusWide))).trans modulusValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.left))).trans leftValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.negatedRight))).trans rightValue)
    exact exactStore.trans (congrArg
      (exposureWrite inverseSuccess candidate reconstruction (transport.restrict before)) actual)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
