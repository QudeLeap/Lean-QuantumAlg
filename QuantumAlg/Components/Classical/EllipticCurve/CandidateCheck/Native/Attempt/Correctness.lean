/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery.Correctness

/-!
# Original first-success latches of one actual attempt

The original six stages preserve a prior accepted candidate. Otherwise they
select exactly the current original raw-recovery candidate when its point
equation and both success flags hold. The statements use the actual caller
store and explicit seven-cell layout facts. The soundness implication is a
single-step invariant preservation theorem, not a new promise on an executed
algorithm's initial result.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Every original structural read outside the seven persistent destinations is unchanged. -/
theorem attemptStore_preserves_read
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) (hidden : model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape)
    (free : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key, accepted.key, selected.key], key ∉ observed.storageKeys) :
    (attemptStore curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected (before, hidden)).read observed =
        before.read observed := by
  rw [attemptStore_eq]
  rw [FirstAccepted.selectionWrite_read_other _ accepted selected _ observed
    (free accepted.key (by simp)) (free selected.key (by simp))]
  apply recoveryStore_preserves_read _ _ _ _ _ _ _ _ _ _ _ _ observed
  intro key member
  exact free key (by simp only [List.mem_cons] at member ⊢; tauto)

private theorem attempt_latches
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) (hidden : model.HiddenState)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key, accepted.key, selected.key].Nodup) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
    let checked := recoveryStore curve modulus sample base target inverseSuccess candidate
      reconstruction scalarResult targetAccepted (before, hidden)
    let after := attemptStore curve modulus sample base target inverseSuccess candidate
      reconstruction scalarResult targetAccepted accepted selected (before, hidden)
    (after.read (.storage accepted.toCStorageRef)).toBool =
        ((before.read (.storage accepted.toCStorageRef)).toBool ||
          (checked.read (.storage targetAccepted.toCStorageRef)).toBool) ∧
      after.read (.storage selected.toCStorageRef) =
        if (!(before.read (.storage accepted.toCStorageRef)).toBool) &&
            (checked.read (.storage targetAccepted.toCStorageRef)).toBool then
          raw.second.first else before.read (.storage selected.toCStorageRef) := by
  have appended : ([inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key] ++ [accepted.key, selected.key]).Nodup := distinct
  have separate := List.nodup_append.mp appended
  have different : accepted.key ≠ selected.key := by
    intro equality
    have last := separate.2.1
    simp [equality] at last
  let checked := recoveryStore curve modulus sample base target inverseSuccess candidate
    reconstruction scalarResult targetAccepted (before, hidden)
  have acceptedRead : checked.read (.storage accepted.toCStorageRef) =
      before.read (.storage accepted.toCStorageRef) := by
    apply recoveryStore_preserves_read _ _ _ _ _ _ _ _ _ _ _ _
      (.storage accepted.toCStorageRef)
    intro key member
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      separate.2.2 key member accepted.key (by simp)
  have selectedRead : checked.read (.storage selected.toCStorageRef) =
      before.read (.storage selected.toCStorageRef) := by
    apply recoveryStore_preserves_read _ _ _ _ _ _ _ _ _ _ _ _
      (.storage selected.toCStorageRef)
    intro key member
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      separate.2.2 key member selected.key (by simp)
  have observations := recoveryStore_observations curve modulus sample base target
    inverseSuccess candidate reconstruction scalarResult targetAccepted before hidden separate.1
  have candidateRead : checked.read (.storage candidate.toCStorageRef) =
      (FiniteCyclicDLP.RawRecovery.outputCells modulus
        (FiniteCyclicDLP.RawRecovery.Native.preparationInput
          (before.read sample))).second.first := observations.2.1
  have latches := FirstAccepted.selectionWrite_latches
    ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩
    accepted selected different checked
  have acceptedEquation :
      ((attemptStore curve modulus sample base target inverseSuccess candidate reconstruction
        scalarResult targetAccepted accepted selected (before, hidden)).read
          (.storage accepted.toCStorageRef)).toBool =
        ((checked.read (.storage accepted.toCStorageRef)).toBool ||
          (checked.read (.storage targetAccepted.toCStorageRef)).toBool) := by
    rw [attemptStore_eq]
    exact latches.1
  have selectedEquation :
      (attemptStore curve modulus sample base target inverseSuccess candidate reconstruction
        scalarResult targetAccepted accepted selected (before, hidden)).read
          (.storage selected.toCStorageRef) =
        if (!(checked.read (.storage accepted.toCStorageRef)).toBool) &&
            (checked.read (.storage targetAccepted.toCStorageRef)).toBool then
          checked.read (.storage candidate.toCStorageRef)
        else checked.read (.storage selected.toCStorageRef) := by
    rw [attemptStore_eq]
    exact latches.2
  constructor
  · rw [acceptedRead] at acceptedEquation
    exact acceptedEquation
  · simpa only [acceptedRead, selectedRead, candidateRead] using selectedEquation

/-- Actual acceptance and selection are exactly the original first-success rule. -/
theorem attemptStore_latches
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) (hidden : model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve (before.read base) basePoint)
    (targetRep : PointRepresents curve (before.read target) targetPoint)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key, accepted.key, selected.key].Nodup)
    (baseFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ base.storageKeys)
    (targetFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ target.storageKeys) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read sample))
    let eligible := raw.second.first.toNat • basePoint = targetPoint ∧
      raw.first.toBool = true ∧ raw.second.second.toBool = true
    let after := attemptStore curve modulus sample base target inverseSuccess candidate
      reconstruction scalarResult targetAccepted accepted selected (before, hidden)
    ((after.read (.storage accepted.toCStorageRef)).toBool = true ↔
        (before.read (.storage accepted.toCStorageRef)).toBool = true ∨ eligible) ∧
      after.read (.storage selected.toCStorageRef) =
        if (before.read (.storage accepted.toCStorageRef)).toBool then
          before.read (.storage selected.toCStorageRef)
        else if eligible then raw.second.first
          else before.read (.storage selected.toCStorageRef) := by
  have appended : ([inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key] ++ [accepted.key, selected.key]).Nodup := distinct
  have check := recoveryStore_accepts_iff curve modulus sample base target inverseSuccess
    candidate reconstruction scalarResult targetAccepted before hidden basePoint targetPoint
    baseRep targetRep (List.nodup_append.mp appended).1 baseFree targetFree
  have latches := attempt_latches curve modulus sample base target inverseSuccess candidate
    reconstruction scalarResult targetAccepted accepted selected before hidden distinct
  dsimp only at check latches ⊢
  constructor
  · rw [latches.1, Bool.or_eq_true, check]
  · rw [latches.2]
    by_cases already : (before.read (.storage accepted.toCStorageRef)).toBool = true
    · simp [already]
    · have absent : (before.read (.storage accepted.toCStorageRef)).toBool = false :=
        Bool.eq_false_iff.mpr already
      by_cases eligible : ((recoveryStore curve modulus sample base target inverseSuccess candidate
          reconstruction scalarResult targetAccepted (before, hidden)).read
            (.storage targetAccepted.toCStorageRef)).toBool = true
      · simp [absent, eligible, check.mp eligible]
      · have ineligible := mt check.mpr eligible
        simp [absent, eligible, ineligible]

/-- A sound prior latch remains sound after this actual attempt, as a local loop invariant. -/
theorem attemptStore_preserves_soundness
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx) (hidden : model.HiddenState)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve (before.read base) basePoint)
    (targetRep : PointRepresents curve (before.read target) targetPoint)
    (distinct : [inverseSuccess.key, candidate.key, reconstruction.key, scalarResult.key,
      targetAccepted.key, accepted.key, selected.key].Nodup)
    (baseFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ base.storageKeys)
    (targetFree : ∀ key ∈ [inverseSuccess.key, candidate.key, reconstruction.key,
      scalarResult.key], key ∉ target.storageKeys)
    (priorSound : (before.read (.storage accepted.toCStorageRef)).toBool = true →
      (before.read (.storage selected.toCStorageRef)).toNat • basePoint = targetPoint)
    (acceptedNow : ((attemptStore curve modulus sample base target inverseSuccess candidate
      reconstruction scalarResult targetAccepted accepted selected (before, hidden)).read
        (.storage accepted.toCStorageRef)).toBool = true) :
    ((attemptStore curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected (before, hidden)).read
        (.storage selected.toCStorageRef)).toNat • basePoint = targetPoint := by
  have latches := attemptStore_latches curve modulus sample base target inverseSuccess candidate
    reconstruction scalarResult targetAccepted accepted selected before hidden basePoint targetPoint
    baseRep targetRep distinct baseFree targetFree
  dsimp only at latches
  rw [latches.2]
  by_cases already : (before.read (.storage accepted.toCStorageRef)).toBool = true
  · rw [if_pos already]
    exact priorSound already
  · have eligible := (latches.1.mp acceptedNow).resolve_left already
    rw [if_neg already, if_pos eligible]
    exact eligible.1

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
