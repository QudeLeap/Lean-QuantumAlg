/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Range
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding.Observation
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Sound retained values along the actual paid-nearest loop

Actual nearest recovery and point verification preserve the selected word's
canonical range and natural-scalar point equation.  The sampler retains the
same first-success pair, and every actual prefix keeps the admitted borrowed
public points.  Complete earlier History and external Reference remain in
the physical execution; caller initialization and sampling independence are
not premises.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

private lemma persistentAttempt_store_support
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (predicate outputPredicate : Store (persistentCtx ctx width scalarWidth) → Prop)
    (updates : ∀ before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState,
      predicate before.1 →
      outputPredicate (persistentAttemptStore (environment := environment) curve modulus sample
        base target before))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (holds : ∀ entry, 0 < (state.block entry).mass → predicate entry.1)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × (H × (persistentAttempt curve modulus sample base target).Path)))
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute environment
      Reference
      state).block result).mass) : outputPredicate result.1 := by
  obtain ⟨record, execution, stores⟩ := attemptInto_actualRecord (environment := environment)
    curve modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  have actual := execution Reference state
  change (persistentAttempt curve modulus sample base target).execute environment Reference
    state = _ at actual
  rw [actual] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  rw [← equality]
  dsimp only
  rw [stores]
  rw [← persistentAttemptStore_eq]
  exact updates (original.1, original.2.1) (holds original present)

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
lemma persistentAttempt_preserves_validity
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
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute environment
      Reference
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
lemma persistentAttempt_preserves_selected_lt
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
    (positive : 0 < (((persistentAttempt curve modulus sample base target).execute environment
      Reference
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
private lemma sampleUnderPersistent_supported_selectedBound
    (sampleCode : Circuit model ctx ctx false)
    (width scalarWidth : Nat) (modulus : ModulusSpec scalarWidth) :
    PreservesStore (environment := environment) (sampleUnderPersistent sampleCode width scalarWidth)
      (selectedBound modulus) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  exact candidateCheck_sampleUnderPersistent_latches_property sampleCode width scalarWidth state
    (fun pair => pair.2.toNat < modulus.modulus) holds result positive

private lemma persistentAttempt_supported_selectedBound
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    PreservesStore (environment := environment) (persistentAttempt curve modulus sample base target)
      (selectedBound modulus) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  exact persistentAttempt_preserves_selected_lt curve modulus sample base target
    state holds result positive

/-- The actual sampling and checked recovery preserve the modulus bound
of the retained selected word on every positive output block. -/
lemma sampledAttempt_preserves_selected_lt
    (sampleCode : Circuit model ctx ctx false)
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
        (H × (sampledAttempt sampleCode curve modulus sample base target).Path)))
    (positive : 0 < (((sampledAttempt sampleCode curve modulus sample base
      target).execute environment Reference state).block result).mass) :
    (result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat <
      modulus.modulus := by
  exact preservesStore_seq
    (sampleUnderPersistent sampleCode width scalarWidth)
    (persistentAttempt curve modulus sample base target) (selectedBound modulus)
    (sampleUnderPersistent_supported_selectedBound sampleCode width scalarWidth modulus)
    (persistentAttempt_supported_selectedBound curve modulus sample base target)
    state holds result positive

/-- Sampling preserves the accepted selection, and a subsequent actual
checked recovery preserves its scalar equation whenever the sampled public
points retain their admitted interpretations. -/
lemma sampledAttempt_preserves_validity
    (sampleCode : Circuit model ctx ctx false)
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
      0 < (((sampleUnderPersistent sampleCode width scalarWidth).execute environment Reference
        state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target))
          targetPoint)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState ×
        (H × (sampledAttempt sampleCode curve modulus sample base target).Path)))
    (positive : 0 < (((sampledAttempt sampleCode curve modulus sample base
      target).execute environment Reference state).block result).mass) :
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
      0 < (((sampleUnderPersistent sampleCode width scalarWidth).execute environment Reference
        state).block entry).mass →
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true →
        (entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint) := by
    intro entry present
    exact candidateCheck_sampleUnderPersistent_latches_property sampleCode width scalarWidth state
      (fun pair => pair.1 = true → pair.2.toNat • basePoint = targetPoint)
      (fun previous source => (holds previous source).2.2) entry present
  have checked := persistentAttempt_preserves_validity (environment := environment)
    curve modulus sample base target
    basePoint targetPoint
    ((sampleUnderPersistent sampleCode width scalarWidth).execute environment Reference state)
    (fun entry source => ⟨(localPoints entry source).1, (localPoints entry source).2,
      localSound entry source⟩) original present
  rw [← equality]
  exact checked

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
