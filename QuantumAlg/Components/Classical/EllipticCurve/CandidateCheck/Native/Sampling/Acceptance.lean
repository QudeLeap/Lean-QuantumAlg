/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Observation

/-!
# The current eligible stored sample enters actual first acceptance

The original raw-recovery flags and natural-scalar point equation determine
eligibility. On a previously unaccepted branch, the actual checked attempt
writes that sample's original recovered word to the persistent selection.
The statements apply to complete positive State blocks and keep arbitrary
Reference systems and histories. No probability or future-sample assumption
is used.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

private def currentEligible (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    (before : Store (persistentCtx ctx width scalarWidth)) : Prop :=
  PointRepresents curve (before.read (persistentInput width scalarWidth base)) basePoint ∧
    PointRepresents curve (before.read (persistentInput width scalarWidth target)) targetPoint ∧
    (before.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
      false ∧
    SampleAccepted curve modulus basePoint targetPoint
      (before.read (persistentInput width scalarWidth sample))

private theorem currentEligible_store
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (eligible : currentEligible curve modulus sample base target basePoint targetPoint before.1) :
    let after := persistentAttemptStore curve modulus sample base target before
    (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        (FiniteCyclicDLP.RawRecovery.outputCells modulus
          (FiniteCyclicDLP.RawRecovery.Native.preparationInput
            (before.1.read (persistentInput width scalarWidth sample)))).second.first := by
  have latches := persistentAttemptStore_latches curve modulus sample base target before
    basePoint targetPoint eligible.1 eligible.2.1
  dsimp only at latches ⊢
  refine ⟨latches.1.mpr (Or.inr eligible.2.2.2), ?_⟩
  simpa only [eligible.2.2.1, Bool.false_eq_true, if_false, if_pos eligible.2.2.2] using latches.2

private theorem persistentAttempt_store_support
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (predicate outputPredicate : Store (persistentCtx ctx width scalarWidth) → Prop)
    (updates : ∀ before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState,
      predicate before.1 →
      outputPredicate (persistentAttemptStore curve modulus sample base target before))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate entry.1)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute Reference
      state).block result).mass) : outputPredicate result.1 := by
  obtain ⟨record, execution, stores⟩ := attemptInto_actualRecord curve modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  have actual := execution Reference state
  change (persistentAttempt curve modulus sample base target).execute Reference state = _ at actual
  rw [actual] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  rw [← equality]
  dsimp only
  rw [stores]
  rw [← persistentAttemptStore_eq]
  exact updates (original.1, original.2.1) (holds original present)

/-- A current eligible sample is accepted and its original recovered word is actually selected. -/
theorem persistentAttempt_accepts_current_supported
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint ∧
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        false ∧
      SampleAccepted curve modulus basePoint targetPoint
        (entry.1.read (persistentInput width scalarWidth sample)))
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute Reference
      state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        (FiniteCyclicDLP.RawRecovery.outputCells modulus
          (FiniteCyclicDLP.RawRecovery.Native.preparationInput
            (result.1.read (persistentInput width scalarWidth sample)))).second.first := by
  refine persistentAttempt_store_support curve modulus sample base target
    (currentEligible curve modulus sample base target basePoint targetPoint)
    (fun store =>
      (store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        (FiniteCyclicDLP.RawRecovery.outputCells modulus
          (FiniteCyclicDLP.RawRecovery.Native.preparationInput
            (store.read (persistentInput width scalarWidth sample)))).second.first) ?_
    state holds result positive
  intro before eligible
  have kept := currentEligible_store curve modulus sample base target basePoint targetPoint
    before eligible
  rw [persistentAttemptStore_preserves_read curve modulus sample base target before sample]
  exact kept

/-- An explicit equality for the original raw candidate supplies the same actual selected word. -/
theorem persistentAttempt_selects_word_supported
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint ∧
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        false ∧
      SampleAccepted curve modulus basePoint targetPoint
        (entry.1.read (persistentInput width scalarWidth sample)) ∧
      (FiniteCyclicDLP.RawRecovery.outputCells modulus
        (FiniteCyclicDLP.RawRecovery.Native.preparationInput
          (entry.1.read (persistentInput width scalarWidth sample)))).second.first = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute Reference
      state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        wanted := by
  let predicate := fun before : Store (persistentCtx ctx width scalarWidth) =>
    currentEligible curve modulus sample base target basePoint targetPoint before ∧
      (FiniteCyclicDLP.RawRecovery.outputCells modulus
        (FiniteCyclicDLP.RawRecovery.Native.preparationInput
          (before.read (persistentInput width scalarWidth sample)))).second.first = wanted
  have originalSupport : ∀ entry, 0 < (state.block entry).mass → predicate entry.1 := by
    intro entry positive
    have eligible := holds entry positive
    exact ⟨⟨eligible.1, eligible.2.1, eligible.2.2.1, eligible.2.2.2.1⟩, eligible.2.2.2.2⟩
  refine persistentAttempt_store_support curve modulus sample base target predicate
    (fun store =>
      (store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted) ?_
    state originalSupport result positive
  intro before eligible
  have kept := currentEligible_store curve modulus sample base target basePoint targetPoint before
    eligible.1
  exact ⟨kept.1, kept.2.trans eligible.2⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
