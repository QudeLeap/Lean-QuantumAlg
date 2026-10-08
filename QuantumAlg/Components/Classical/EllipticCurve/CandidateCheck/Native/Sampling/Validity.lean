/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Acceptance
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Range
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Local
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Sound selected values in actual persistent recovery blocks

The original stored soundness and range invariants lift through the same
actual checked attempt. Positive blocks retain both original public-point
interpretations. The actual final option pack exposes the same selected
word, so any established property of an accepted selection holds of every
returned value. No independence or probability assumption is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

private def validSelection (curve : CurveSpec width)
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    (store : Store (persistentCtx ctx width scalarWidth)) : Prop :=
  PointRepresents curve (store.read (persistentInput width scalarWidth base)) basePoint ∧
    PointRepresents curve (store.read (persistentInput width scalarWidth target)) targetPoint ∧
      ((store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint)

/-- Every positive actual checked block retains the original natural-scalar soundness invariant. -/
theorem persistentAttempt_preserves_validity
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint ∧
        ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
            true →
          (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute Reference
      state).block result).mass) :
    PointRepresents curve (result.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (result.1.read (persistentInput width scalarWidth target)) targetPoint ∧
        ((result.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
            true →
          (result.1.read
            (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint) := by
  refine persistentAttempt_store_support curve modulus sample base target
    (validSelection curve base target basePoint targetPoint)
    (validSelection curve base target basePoint targetPoint) ?_ state holds result positive
  intro before prior
  refine ⟨?_, ?_, ?_⟩
  · rw [persistentAttemptStore_preserves_read]
    exact prior.1
  · rw [persistentAttemptStore_preserves_read]
    exact prior.2.1
  · intro acceptedNow
    exact persistentAttemptStore_preserves_soundness curve modulus sample base target before
      basePoint targetPoint prior.1 prior.2.1 prior.2.2 acceptedNow

/-- The original selected-word modulus bound also holds in every positive actual output block. -/
theorem persistentAttempt_preserves_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute Reference
      state).block result).mass) :
    (result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
      modulus.modulus := by
  exact persistentAttempt_store_support curve modulus sample base target
    (fun store => (store.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat < modulus.modulus)
    (fun store => (store.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat < modulus.modulus)
    (persistentAttemptStore_selected_lt curve modulus sample base target)
    state holds result positive

attribute [local irreducible] persistentCtx packBatchResultStep

private def selectedBound (modulus : ModulusSpec scalarWidth)
    (store : Store (persistentCtx ctx width scalarWidth)) : Prop :=
  (store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
    modulus.modulus

omit [BitWord.Selected model] in
private theorem underPersistent_supported_selectedBound
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (width scalarWidth : Nat) (modulus : ModulusSpec scalarWidth) :
    PreservesStore (underPersistent sampleCode supported width scalarWidth)
      (selectedBound modulus) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  exact underPersistent_selected_property sampleCode supported width scalarWidth
    (fun word => word.toNat < modulus.modulus) state holds result positive

private theorem persistentAttempt_supported_selectedBound
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    PreservesStore (persistentAttempt curve modulus sample base target)
      (selectedBound modulus) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  exact persistentAttempt_preserves_selected_lt curve modulus sample base target
    state holds result positive

/-- The actual local sampling and checked recovery preserve the modulus bound
of the retained selected word on every positive output block. -/
theorem sampledAttempt_preserves_selected_lt
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState ×
        (H × (sampledAttempt sampleCode supported curve modulus sample base target).Path)))
    (positive : 0 < (((sampledAttempt sampleCode supported curve modulus sample base
      target).execute Reference state).block result).mass) :
    (result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
      modulus.modulus := by
  exact preservesStore_seq
    (underPersistent sampleCode supported width scalarWidth)
    (persistentAttempt curve modulus sample base target) (selectedBound modulus)
    (underPersistent_supported_selectedBound sampleCode supported width scalarWidth modulus)
    (persistentAttempt_supported_selectedBound curve modulus sample base target)
    state holds result positive

/-- Local sampling preserves the accepted selection, and a subsequent actual
checked recovery preserves its scalar equation whenever the sampled public
points retain their admitted interpretations. -/
theorem sampledAttempt_preserves_validity
    (sampleCode : Circuit model ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint ∧
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint))
    (localPoints : ∀ entry,
      0 < (((underPersistent sampleCode supported width scalarWidth).execute Reference
        state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target))
          targetPoint)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState ×
        (H × (sampledAttempt sampleCode supported curve modulus sample base target).Path)))
    (positive : 0 < (((sampledAttempt sampleCode supported curve modulus sample base
      target).execute Reference state).block result).mass) :
    PointRepresents curve (result.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (result.1.read (persistentInput width scalarWidth target)) targetPoint ∧
      ((result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint) := by
  unfold sampledAttempt at positive
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have localSound : ∀ entry,
      0 < (((underPersistent sampleCode supported width scalarWidth).execute Reference
        state).block entry).mass →
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint) := by
    intro entry present
    exact underPersistent_latches_property sampleCode supported width scalarWidth
      (fun pair => pair.1 = true → pair.2.toNat • basePoint = targetPoint)
      state (fun previous source => (holds previous source).2.2) entry present
  have checked := persistentAttempt_preserves_validity curve modulus sample base target
    basePoint targetPoint
    ((underPersistent sampleCode supported width scalarWidth).execute Reference state)
    (fun entry source => ⟨(localPoints entry source).1, (localPoints entry source).2,
      localSound entry source⟩) original present
  rw [← equality]
  exact checked

private theorem packing_store_property (property : (CShape.unsignedWord scalarWidth).Value → Prop)
    (before : Store (persistentCtx ctx width scalarWidth))
    (holds : (before.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
        property (before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (value : (CShape.unsignedWord scalarWidth).Value)
    (output : (packBatchResultStep ctx width scalarWidth before).1.read
      (batchResultRead ctx width scalarWidth) = .optionSome value) : property value := by
  rw [packBatchResultStep_output] at output
  cases flag : before.read (.storage
      (persistentAccepted ctx width scalarWidth).toCStorageRef) with
  | bit flagValue =>
      cases flagValue with
      | false =>
          simp only [flag, CShape.packOption_false] at output
          cases output
      | true =>
          simp only [flag, CShape.packOption_true, CShape.Value.optionSome.injEq] at output
          rw [← output]
          exact holds (by simp only [flag, CShape.Value.toBool])

local instance : DecidableEq Bool := Classical.decEq Bool

/-- The actual retained option carries every proved property of its same accepted selected word. -/
theorem packBatchResult_supported_property
    (property : (CShape.unsignedWord scalarWidth).Value → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        property (entry.1.read (.storage
          (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (packBatchResult ctx width scalarWidth).Path)))
    (positive : 0 < (((packBatchResult ctx width scalarWidth).execute Reference state).block
      result).mass) (value : (CShape.unsignedWord scalarWidth).Value)
    (output : result.1.read (batchResultRead ctx width scalarWidth) = .optionSome value) :
    property value := by
  classical
  let check : (CShape.option (.unsignedWord scalarWidth)).Value → Bool := fun packed =>
    match packed with
    | .optionNone => true
    | .optionSome selected => decide (property selected)
  let observe := fun entry : Store (batchResultCtx ctx width scalarWidth) × H =>
    check (entry.1.read (batchResultRead ctx width scalarWidth))
  rw [packBatchResult_execute] at positive
  have observedPositive : 0 < ((packBatchResultObserved ctx width scalarWidth observe
      Reference state).block (observe (result.1, result.2.2.1))).mass := by
    unfold packBatchResultObserved
    exact (mapped_positive _ _ _ _).mpr ⟨result, rfl, positive⟩
  rw [packBatchResult_observe] at observedPositive
  have expectedConstant : packBatchResultExpected ctx width scalarWidth observe Reference state =
      state.mapClassical (fun _ => true) := by
    unfold packBatchResultExpected
    apply ExecutionState.mapClassical_eq_of_support
    intro entry present
    cases packed : (packBatchResultStep ctx width scalarWidth entry.1).1.read
        (batchResultRead ctx width scalarWidth) with
    | optionNone => simp [observe, check, packed]
    | optionSome selected =>
        have good := packing_store_property property entry.1 (holds entry present)
          selected packed
        simp [observe, check, packed, good]
  rw [expectedConstant] at observedPositive
  have checked : observe (result.1, result.2.2.1) = true := by
    by_contra different
    have opposite : true ≠ observe (result.1, result.2.2.1) := by
      intro equality
      exact different equality.symm
    rw [ExecutionState.mapClassical_block_mass] at observedPositive
    simp only [opposite, if_false, Finset.sum_const_zero, lt_self_iff_false]
      at observedPositive
  simpa only [observe, output, check, decide_eq_true_eq] using checked

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
