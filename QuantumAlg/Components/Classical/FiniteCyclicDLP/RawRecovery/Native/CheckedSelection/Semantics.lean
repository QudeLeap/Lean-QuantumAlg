/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Selection.Original
import all QuantumAlg.Components.Classical.NumberTheory.Checked.Native.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Initialization.Restricted

/-!
# Actual checked inversion and selected original recovery

The actual checked-inverse record feeds the status-selected recovery on its
real returned store. Its successful inverse is proved by that actual checked
subcall. Two genuine lexical output cells discharge the input separation
conditions and remain live until optional packing finishes. Their release
preserves every caller read outside the original optional-result destination.
The complete quantum-reference equation and original output use one record.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual checked output words feed the original optional recovery on the same store. -/
theorem checkedSelectionBody_actualRecord (spec : ModulusSpec width)
    (left negatedRight : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (success : CWriteRef ctx .bit) (inverse : CWriteRef ctx (.unsignedWord width))
    (result : CWriteRef ctx (OutputShape width))
    (successLeft : success.key ∉ left.storageKeys)
    (inverseLeft : inverse.key ∉ left.storageKeys)
    (successRight : success.key ∉ negatedRight.storageKeys)
    (inverseRight : inverse.key ∉ negatedRight.storageKeys)
    (successModulus : success.key ∉ modulus.storageKeys)
    (inverseModulus : inverse.key ∉ modulus.storageKeys) :
    ∃ record : Store ctx → Store ctx ×
        (checkedSelectionBody spec left negatedRight modulus success inverse result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (checkedSelectionBody spec left negatedRight modulus success inverse result).execute
          Reference state = state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          success.key ∉ other.storageKeys → inverse.key ∉ other.storageKeys →
            result.key ∉ other.storageKeys → (record before).1.read other = before.read other) ∧
        ∀ original : CShape.Value (InputShape width),
          (before.read modulus).toNat = spec.modulus →
          (before.read left).toNat = (normalize spec original).left.val →
          (before.read negatedRight).toNat = (negateRight spec (normalize spec original)).val →
          (record before).1.read (scaleRead result) =
            encodedRawOutput spec (RawRecovery.outputOf spec original) := by
  obtain ⟨checkedRecord, checkedEquation, checkedCorrect⟩ :=
    NumberTheory.Checked.Native.withCheckedInverse_actualRecord spec left success inverse
  let recoveryInput := CInputRef.product left (.product negatedRight (scaleRead inverse))
  refine ⟨Circuit.sequenceRecord _ _ checkedRecord
    (withSelectedRecoveryStep recoveryInput modulus (scaleRead success) result),
    Circuit.execute_sequenceRecord _ _ _ _ checkedEquation
      (withSelectedRecovery_execute recoveryInput modulus (scaleRead success) result), ?_⟩
  intro before
  let checked := (checkedRecord before).1
  constructor
  · intro shape other successFree inverseFree resultFree
    exact (withSelectedRecovery_read_other recoveryInput modulus (scaleRead success) result
      other resultFree checked).trans ((checkedCorrect before).1 other successFree inverseFree)
  · intro original modulusValue leftValue rightValue
    have leftRead : checked.read left = before.read left :=
      (checkedCorrect before).1 left successLeft inverseLeft
    have rightRead : checked.read negatedRight = before.read negatedRight :=
      (checkedCorrect before).1 negatedRight successRight inverseRight
    have modulusRead : checked.read modulus = before.read modulus :=
      (checkedCorrect before).1 modulus successModulus inverseModulus
    have actual := (checkedCorrect before).2 (normalize spec original).left leftValue
    have selected := withSelectedRecovery_value recoveryInput modulus (scaleRead success)
      result checked
    change (withSelectedRecoveryStep recoveryInput modulus (scaleRead success) result
      checked).1.read (scaleRead result) =
        (if (checked.read (scaleRead success)).toBool then .optionSome
          (NormalizedRecovery.Native.recoveryValue (checked.read left) (checked.read negatedRight)
            (checked.read (scaleRead inverse)) (checked.read modulus)) else .optionNone) at selected
    refine selected.trans (selectedRecoveryValue_original spec original
      (checked.read (scaleRead success)) (checked.read left) (checked.read negatedRight)
      (checked.read (scaleRead inverse)) (checked.read modulus)
      ((congrArg CShape.Value.toNat modulusRead).trans modulusValue)
      ((congrArg CShape.Value.toNat leftRead).trans leftValue)
      ((congrArg CShape.Value.toNat rightRead).trans rightValue) actual.1 actual.2.1)

/-- Real checked output allocation removes all scratch and input-separation caller premises. -/
theorem withCheckedSelection_actualRecord (spec : ModulusSpec width)
    (refs : PreparationRefs ctx width) (result : CWriteRef ctx (OutputShape width)) :
    ∃ record : Store ctx → Store ctx × (withCheckedSelection spec refs result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (withCheckedSelection spec refs result).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          result.key ∉ other.storageKeys → (record before).1.read other = before.read other) ∧
        ∀ original : CShape.Value (InputShape width),
          (before.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
          (before.read (scaleRead refs.left)).toNat = (normalize spec original).left.val →
          (before.read (scaleRead refs.negatedRight)).toNat =
            (negateRight spec (normalize spec original)).val →
          (record before).1.read (scaleRead result) =
            encodedRawOutput spec (RawRecovery.outputOf spec original) := by
  let Post (before after : Store ctx) : Prop :=
    (∀ {shape : CShape} (other : CInputRef ctx shape), result.key ∉ other.storageKeys →
      after.read other = before.read other) ∧
    ∀ original : CShape.Value (InputShape width),
      (before.read (scaleRead refs.modulusWide)).toNat = spec.modulus →
      (before.read (scaleRead refs.left)).toNat = (normalize spec original).left.val →
      (before.read (scaleRead refs.negatedRight)).toNat =
        (negateRight spec (normalize spec original)).val →
      after.read (scaleRead result) = encodedRawOutput spec (RawRecovery.outputOf spec original)
  unfold withCheckedSelection
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
  obtain ⟨record, equation, correct⟩ := checkedSelectionBody_actualRecord spec
    (transport.liftInput (scaleRead refs.left))
    (transport.liftInput (scaleRead refs.negatedRight))
    (transport.liftInput (scaleRead refs.modulusWide))
    (checkedSuccessCell cells) (checkedInverseCell cells) (transport.liftWrite result)
    (free (scaleRead refs.left)).1 (free (scaleRead refs.left)).2
    (free (scaleRead refs.negatedRight)).1 (free (scaleRead refs.negatedRight)).2
    (free (scaleRead refs.modulusWide)).1 (free (scaleRead refs.modulusWide)).2
  refine ⟨record, equation, ?_⟩
  intro before _initialized
  have entered : transport.ReadsAs (transport.restrict before) before :=
    transport.workspaceTransport_restrict_readsAs before
  have returned : transport.ReadsAs (transport.restrict (record before).1) (record before).1 :=
    transport.workspaceTransport_restrict_readsAs (record before).1
  constructor
  · intro shape other resultFree
    have frame := (correct before).1 (transport.liftInput other)
      (free other).1 (free other).2
      (by simpa only [transport.liftWrite_key, transport.liftInput_storageKeys] using resultFree)
    exact (returned other).symm.trans (frame.trans (entered other))
  · intro original modulusValue leftValue rightValue
    have actual := (correct before).2 original
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.modulusWide))).trans modulusValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.left))).trans leftValue)
      ((congrArg CShape.Value.toNat (entered (scaleRead refs.negatedRight))).trans rightValue)
    have outputRead : (record before).1.read (scaleRead (transport.liftWrite result)) =
        (transport.restrict (record before).1).read (scaleRead result) := by
      simpa only [scaleRead, transport.liftWrite_input] using returned (scaleRead result)
    exact outputRead.symm.trans actual

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
