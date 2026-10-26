/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Persistent.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Store

/-!
# Paid nearest recovery through actual candidate verification and first-success selection

The existing native verifier and selector consume the actual nearest decoder's
three exposed cells.  All chronological stores, path records, caller reads,
Reference matrices and prior History labels remain part of the same execution.
The generic truncated-range decoder and its existing consumers are unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The original raw observations satisfy the complete natural-scalar candidate condition. -/
def SampleAccepted (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) : Prop :=
  let raw := FiniteCyclicDLP.RawRecovery.Nearest.outputCellsInput modulus
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
    let raw := FiniteCyclicDLP.RawRecovery.Nearest.outputCellsInput modulus
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


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
