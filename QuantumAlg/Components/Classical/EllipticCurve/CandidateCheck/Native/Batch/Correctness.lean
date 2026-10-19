/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Store

/-!
# Original sample conditions throughout the actual persistent loop

Real persistent allocation supplies every internal separation fact. Each
attempt preserves all original samples and point inputs, so acceptance is
exactly prior acceptance or an original sample satisfying the original raw
recovery and point-check condition. The actual fresh false latch eliminates
prior acceptance at the initialized entry. Soundness is preserved as a local
loop invariant without a caller inverse, secret or workspace promise.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The original raw observations satisfy the complete natural-scalar candidate condition. -/
def SampleAccepted (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) : Prop :=
  let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
    (FiniteCyclicDLP.RawRecovery.Native.preparationInput sample)
  raw.second.first.toNat • basePoint = targetPoint ∧
    raw.first.toBool = true ∧ raw.second.second.toBool = true

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

private lemma attemptKeys_permutation {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    [(persistentInverseSuccess ctx width scalarWidth).key,
      (persistentCandidate ctx width scalarWidth).key,
      (persistentReconstruction ctx width scalarWidth).key,
      (persistentScalar ctx width scalarWidth).key,
      (persistentTargetAccepted ctx width scalarWidth).key,
      (persistentAccepted ctx width scalarWidth).key,
      (persistentSelected ctx width scalarWidth).key].Perm
        (persistentKeys ctx width scalarWidth) := by
  apply List.perm_iff_count.mpr
  intro key
  simp only [persistentKeys, List.count_cons, List.count_nil]
  omega

private lemma attemptKeys_distinct {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width scalarWidth : Nat) :
    [(persistentInverseSuccess ctx width scalarWidth).key,
      (persistentCandidate ctx width scalarWidth).key,
      (persistentReconstruction ctx width scalarWidth).key,
      (persistentScalar ctx width scalarWidth).key,
      (persistentTargetAccepted ctx width scalarWidth).key,
      (persistentAccepted ctx width scalarWidth).key,
      (persistentSelected ctx width scalarWidth).key].Nodup :=
  (attemptKeys_permutation ctx width scalarWidth).nodup_iff.mpr
    (persistentKeys_distinct ctx width scalarWidth)

private lemma persistentAttemptStore_eq
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    persistentAttemptStore (environment := environment) curve modulus sample base target before =
      attemptStore (environment := environment) curve modulus (persistentInput width scalarWidth
        sample)
        (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
        (persistentInverseSuccess ctx width scalarWidth)
        (persistentCandidate ctx width scalarWidth)
        (persistentReconstruction ctx width scalarWidth)
        (persistentScalar ctx width scalarWidth)
        (persistentTargetAccepted ctx width scalarWidth)
        (persistentAccepted ctx width scalarWidth)
        (persistentSelected ctx width scalarWidth) before := by
  exact (Classical.choose_spec (attemptInto_actualRecord (environment := environment) curve modulus
    (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth))).2 before

/-- A real persistent attempt preserves every original structural input. -/
lemma persistentAttemptStore_preserves_read
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape) :
    (persistentAttemptStore (environment := environment) curve modulus sample base target
      before).read
      (persistentInput width scalarWidth observed) =
        before.1.read (persistentInput width scalarWidth observed) := by
  rw [persistentAttemptStore_eq]
  apply attemptStore_preserves_read curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth) before.1 before.2
    (persistentInput width scalarWidth observed)
  intro key member
  exact persistentInput_separate width scalarWidth observed key
    ((attemptKeys_permutation ctx width scalarWidth).mem_iff.mp member)

/-- Actual persistent cells discharge every separation premise of original first acceptance. -/
lemma persistentAttemptStore_latches
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint) :
    let value := before.1.read (persistentInput width scalarWidth sample)
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput value)
    let after := persistentAttemptStore (environment := environment) curve modulus sample base
      target before
    ((after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ↔
      (before.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∨ SampleAccepted curve modulus basePoint targetPoint value) ∧
    after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
      if (before.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool then
        before.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)
      else if SampleAccepted curve modulus basePoint targetPoint value then raw.second.first
        else before.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
  simp only [persistentAttemptStore_eq]
  apply attemptStore_latches curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth) before.1 before.2
    basePoint targetPoint baseRep targetRep (attemptKeys_distinct ctx width scalarWidth)
  all_goals
    intro key member
    apply persistentInput_separate width scalarWidth _ key
    exact (attemptKeys_permutation ctx width scalarWidth).mem_iff.mp
      (List.mem_append_left _ member)

/-- The original natural-scalar soundness invariant survives one real persistent attempt. -/
lemma persistentAttemptStore_preserves_soundness
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint)
    (priorSound : (before.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
      (before.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
        basePoint = targetPoint)
    (acceptedNow : ((persistentAttemptStore (environment := environment) curve modulus sample
      base target before).read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true) :
    ((persistentAttemptStore (environment := environment) curve modulus sample base target
      before).read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
        basePoint = targetPoint := by
  have latches := persistentAttemptStore_latches (environment := environment)
    curve modulus sample base target before
    basePoint targetPoint baseRep targetRep
  dsimp only at latches
  rw [latches.2]
  by_cases already : (before.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true
  · rw [if_pos already]
    exact priorSound already
  · have eligible := (latches.1.mp acceptedNow).resolve_left already
    rw [if_neg already, if_pos eligible]
    exact eligible.1

private lemma fold_preserves_read (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : List (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape) :
    (samples.foldl (fun current sample =>
      persistentAttemptState (environment := environment) curve modulus sample base target
        current) before).1.read
        (persistentInput width scalarWidth observed) =
          before.1.read (persistentInput width scalarWidth observed) := by
  induction samples generalizing before with
  | nil => rfl
  | cons sample rest ih =>
      exact (ih (persistentAttemptState (environment := environment) curve modulus sample base
        target before)).trans
        (persistentAttemptStore_preserves_read curve modulus sample base target before observed)

private lemma fold_accepts_iff (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : List (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint) :
    ((samples.foldl (fun current sample =>
      persistentAttemptState (environment := environment) curve modulus sample base target
        current) before).1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ↔
      (before.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∨ ∃ sample ∈ samples, SampleAccepted curve modulus basePoint targetPoint
          (before.1.read (persistentInput width scalarWidth sample)) := by
  induction samples generalizing before with
  | nil => simp
  | cons sample rest ih =>
      let next := persistentAttemptState (environment := environment) curve modulus sample base
        target before
      have nextStore : next.1 = persistentAttemptStore (environment := environment) curve
        modulus sample base target before :=
        rfl
      have nextBase : PointRepresents curve
          (next.1.read (persistentInput width scalarWidth base)) basePoint := by
        rw [nextStore, persistentAttemptStore_preserves_read]
        exact baseRep
      have nextTarget : PointRepresents curve
          (next.1.read (persistentInput width scalarWidth target)) targetPoint := by
        rw [nextStore, persistentAttemptStore_preserves_read]
        exact targetRep
      have tail := ih next nextBase nextTarget
      have preserved (input : CInputRef ctx
          (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
          SampleAccepted curve modulus basePoint targetPoint
            (next.1.read (persistentInput width scalarWidth input)) ↔
          SampleAccepted curve modulus basePoint targetPoint
            (before.1.read (persistentInput width scalarWidth input)) := by
        rw [nextStore, persistentAttemptStore_preserves_read]
      have head := (persistentAttemptStore_latches (environment := environment)
        curve modulus sample base target before
        basePoint targetPoint baseRep targetRep).1
      simp only [preserved] at tail
      change ((rest.foldl (fun current input =>
        persistentAttemptState (environment := environment) curve modulus input base target
          current) next).1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ↔ _
      rw [tail, nextStore, head]
      simp only [List.mem_cons]
      constructor
      · rintro ((prior | first) | ⟨input, member, accepted⟩)
        · exact Or.inl prior
        · exact Or.inr ⟨sample, Or.inl rfl, first⟩
        · exact Or.inr ⟨input, Or.inr member, accepted⟩
      · rintro (prior | ⟨input, member, accepted⟩)
        · exact Or.inl (Or.inl prior)
        · rcases member with rfl | member
          · exact Or.inl (Or.inr accepted)
          · exact Or.inr ⟨input, member, accepted⟩

private lemma fold_preserves_soundness
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : List (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint)
    (priorSound : (before.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
      (before.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
        basePoint = targetPoint) :
    ((samples.foldl (fun current sample =>
      persistentAttemptState (environment := environment) curve modulus sample base target
        current) before).1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
      ((samples.foldl (fun current sample =>
        persistentAttemptState (environment := environment) curve modulus sample base target
          current) before).1.read
          (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
            basePoint = targetPoint := by
  induction samples generalizing before with
  | nil => exact priorSound
  | cons sample rest ih =>
      apply ih (persistentAttemptState (environment := environment) curve modulus sample base
        target before)
      · change PointRepresents curve
          ((persistentAttemptStore (environment := environment) curve modulus sample base target
            before).read
            (persistentInput width scalarWidth base)) basePoint
        rw [persistentAttemptStore_preserves_read]
        exact baseRep
      · change PointRepresents curve
          ((persistentAttemptStore (environment := environment) curve modulus sample base target
            before).read
            (persistentInput width scalarWidth target)) targetPoint
        rw [persistentAttemptStore_preserves_read]
        exact targetRep
      · exact persistentAttemptStore_preserves_soundness curve modulus sample base target before
          basePoint targetPoint baseRep targetRep priorSound

private lemma repeatedAttemptsStore_fold
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    repeatedAttemptsStore (environment := environment) curve modulus samples base target before =
      ((List.ofFn samples).foldl (fun current sample =>
        persistentAttemptState (environment := environment) curve modulus sample base target
          current) before).1 := by
  unfold repeatedAttemptsStore repeatedAttemptsState
  have updates : List.ofFn (fun index =>
      persistentAttemptState (environment := environment) curve modulus (samples index) base
        target) =
      (List.ofFn samples).map (fun sample =>
        persistentAttemptState (environment := environment) curve modulus sample base target) := by
    rw [List.map_ofFn]
    rfl
  rw [updates, List.foldl_map]

/-- Every original sample and point input is unchanged throughout all actual attempts. -/
lemma repeatedAttemptsStore_preserves_read
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape) :
    (repeatedAttemptsStore (environment := environment) curve modulus samples base target
      before).read
      (persistentInput width scalarWidth observed) =
        before.1.read (persistentInput width scalarWidth observed) := by
  rw [repeatedAttemptsStore_fold]
  exact fold_preserves_read curve modulus (List.ofFn samples) base target before observed

/-- The actual chronological loop accepts exactly prior success or an original eligible sample. -/
lemma repeatedAttemptsStore_accepts_iff
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint) :
    ((repeatedAttemptsStore (environment := environment) curve modulus samples base target
      before).read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ↔
      (before.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∨ ∃ index, SampleAccepted curve modulus basePoint targetPoint
          (before.1.read (persistentInput width scalarWidth (samples index))) := by
  rw [repeatedAttemptsStore_fold, fold_accepts_iff curve modulus (List.ofFn samples)
    base target before basePoint targetPoint baseRep targetRep]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨sample, member, eligible⟩
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨index, eligible⟩
  · rintro ⟨index, eligible⟩
    exact ⟨samples index, List.mem_ofFn.mpr ⟨index, rfl⟩, eligible⟩

/-- Actual fresh initialization removes prior acceptance without a caller zero premise. -/
lemma repeatedAttemptsStore_initial_accepts_iff
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx)
    (hidden : model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve (before.read base) basePoint)
    (targetRep : PointRepresents curve (before.read target) targetPoint) :
    ((repeatedAttemptsStore (environment := environment) curve modulus samples base target
      (persistentInitialStore width scalarWidth before, hidden)).read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ↔
      ∃ index, SampleAccepted curve modulus basePoint targetPoint
        (before.read (samples index)) := by
  have correct := repeatedAttemptsStore_accepts_iff (environment := environment)
    curve modulus samples base target
    (persistentInitialStore width scalarWidth before, hidden) basePoint targetPoint
    (by rw [persistentInitialStore_read]; exact baseRep)
    (by rw [persistentInitialStore_read]; exact targetRep)
  have initial : (persistentInitialStore width scalarWidth before).read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef) = .bit false :=
    persistentInitialStore_accepted width scalarWidth before
  simpa only [initial, CShape.Value.toBool, Bool.false_eq_true, false_or,
    persistentInitialStore_read] using correct

/-- The original natural-scalar soundness invariant holds after every actual loop iteration. -/
lemma repeatedAttemptsStore_preserves_soundness
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.1.read (persistentInput width scalarWidth target)) targetPoint)
    (priorSound : (before.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
      (before.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
        basePoint = targetPoint) :
    ((repeatedAttemptsStore (environment := environment) curve modulus samples base target
      before).read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true →
      ((repeatedAttemptsStore (environment := environment) curve modulus samples base target
        before).read
        (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)).toNat •
          basePoint = targetPoint := by
  rw [repeatedAttemptsStore_fold]
  exact fold_preserves_soundness curve modulus (List.ofFn samples) base target before
    basePoint targetPoint baseRep targetRep priorSound

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
