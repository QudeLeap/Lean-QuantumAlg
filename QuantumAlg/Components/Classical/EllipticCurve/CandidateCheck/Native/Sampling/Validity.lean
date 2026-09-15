/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Acceptance
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Range

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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

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
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint ∧
        ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
            true →
          (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (persistentAttempt curve modulus sample base target).Path))
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
  · exact persistentAttemptStore_preserves_soundness curve modulus sample base target before
      basePoint targetPoint prior.1 prior.2.1 prior.2.2

/-- The original selected-word modulus bound also holds in every positive actual output block. -/
theorem persistentAttempt_preserves_selected_lt
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
        modulus.modulus)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (persistentAttempt curve modulus sample base target).Path))
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

/-- The actual retained option carries every proved property of its same accepted selected word. -/
theorem packBatchResult_supported_property
    (property : (CShape.unsignedWord scalarWidth).Value → Prop)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        property (entry.1.read (.storage
          (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (result : Store (batchResultCtx ctx width scalarWidth) ×
      (H × (packBatchResult ctx width scalarWidth).Path))
    (positive : 0 < (((packBatchResult ctx width scalarWidth).execute Reference state).block
      result).mass) (value : (CShape.unsignedWord scalarWidth).Value)
    (output : result.1.read (batchResultRead ctx width scalarWidth) = .optionSome value) :
    property value := by
  have finalProperty := retainedStep_supported
    (persistentCtx ctx width scalarWidth).canonicalFreshKey
    (.option (.unsignedWord scalarWidth))
    (persistentCtx ctx width scalarWidth).canonicalFreshKey_fresh
    (batchResultOp ctx width scalarWidth)
    (fun store =>
      (store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        property (store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)))
    (fun store => ∀ value, store.read (batchResultRead ctx width scalarWidth) = .optionSome value →
      property value)
    (packing_store_property property) state holds result positive
  exact finalProperty value output

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
