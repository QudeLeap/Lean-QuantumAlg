/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness

/-!
# First-write order in the actual chronological sample loop

The first sample satisfying the original raw-recovery and point-check
condition supplies the selected word. The proof decomposes the actual
`List.ofFn` schedule into its rejected prefix, chosen sample and suffix.
Later real attempts preserve the already accepted word. No secret witness,
uniqueness assumption or separate scan interpreter is introduced.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

private theorem fold_preserves_first
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : List (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth))
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth target)) targetPoint)
    (already : (before.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true) :
    let after := samples.foldl (fun current sample =>
      persistentAttemptStore curve modulus sample base target current) before
    (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
  induction samples generalizing before with
  | nil => exact ⟨already, rfl⟩
  | cons sample rest ih =>
      let next := persistentAttemptStore curve modulus sample base target before
      have nextBase : PointRepresents curve
          (next.read (persistentInput width scalarWidth base)) basePoint := by
        rw [persistentAttemptStore_preserves_read]
        exact baseRep
      have nextTarget : PointRepresents curve
          (next.read (persistentInput width scalarWidth target)) targetPoint := by
        rw [persistentAttemptStore_preserves_read]
        exact targetRep
      have latches := persistentAttemptStore_latches curve modulus sample base target before
        basePoint targetPoint baseRep targetRep
      have nextAccepted : (next.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true :=
        latches.1.mpr (Or.inl already)
      have nextSelected : next.read
          (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
          before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
        rw [latches.2, if_pos already]
      have restResult := ih next nextBase nextTarget nextAccepted
      exact ⟨restResult.1, restResult.2.trans nextSelected⟩

/-- All later actual samples preserve an already accepted first word. -/
theorem repeatedAttemptsStore_preserves_first
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth))
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth target)) targetPoint)
    (already : (before.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true) :
    let after := repeatedAttemptsStore curve modulus samples base target before
    (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
  rw [repeatedAttemptsStore_fold]
  exact fold_preserves_first curve modulus (List.ofFn samples) base target before
    basePoint targetPoint baseRep targetRep already

/-- The first original eligible sample in the actual schedule supplies the final selected word. -/
theorem repeatedAttemptsStore_selected_first
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth))
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth base)) basePoint)
    (targetRep : PointRepresents curve
      (before.read (persistentInput width scalarWidth target)) targetPoint)
    (earlierSamples suffix : List
      (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (chosen : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (order : List.ofFn samples = earlierSamples ++ chosen :: suffix)
    (initial : (before.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false)
    (rejected : ∀ sample ∈ earlierSamples, ¬SampleAccepted curve modulus basePoint targetPoint
      (before.read (persistentInput width scalarWidth sample)))
    (eligible : SampleAccepted curve modulus basePoint targetPoint
      (before.read (persistentInput width scalarWidth chosen))) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput
        (before.read (persistentInput width scalarWidth chosen)))
    let after := repeatedAttemptsStore curve modulus samples base target before
    after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        raw.second.first ∧
      (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true := by
  let preceding := earlierSamples.foldl (fun current sample =>
    persistentAttemptStore curve modulus sample base target current) before
  have precedingBase : PointRepresents curve
      (preceding.read (persistentInput width scalarWidth base)) basePoint := by
    rw [fold_preserves_read]
    exact baseRep
  have precedingTarget : PointRepresents curve
      (preceding.read (persistentInput width scalarWidth target)) targetPoint := by
    rw [fold_preserves_read]
    exact targetRep
  have precedingAccepted : (preceding.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    rcases (fold_accepts_iff curve modulus earlierSamples base target before basePoint targetPoint
      baseRep targetRep).mp accepted with prior | ⟨sample, member, valid⟩
    · simp [initial] at prior
    · exact rejected sample member valid
  have chosenRead : preceding.read (persistentInput width scalarWidth chosen) =
      before.read (persistentInput width scalarWidth chosen) :=
    fold_preserves_read curve modulus earlierSamples base target before chosen
  have chosenEligible : SampleAccepted curve modulus basePoint targetPoint
      (preceding.read (persistentInput width scalarWidth chosen)) := by
    rw [chosenRead]
    exact eligible
  let following := persistentAttemptStore curve modulus chosen base target preceding
  have latches := persistentAttemptStore_latches curve modulus chosen base target preceding
    basePoint targetPoint precedingBase precedingTarget
  have followingAccepted : (following.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true :=
    latches.1.mpr (Or.inr chosenEligible)
  have followingSelected : following.read
      (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
      (FiniteCyclicDLP.RawRecovery.outputCells modulus
        (FiniteCyclicDLP.RawRecovery.Native.preparationInput
          (before.read (persistentInput width scalarWidth chosen)))).second.first := by
    rw [latches.2]
    simp only [precedingAccepted, Bool.false_eq_true, ite_false, if_pos chosenEligible, chosenRead]
  have followingBase : PointRepresents curve
      (following.read (persistentInput width scalarWidth base)) basePoint := by
    rw [persistentAttemptStore_preserves_read]
    exact precedingBase
  have followingTarget : PointRepresents curve
      (following.read (persistentInput width scalarWidth target)) targetPoint := by
    rw [persistentAttemptStore_preserves_read]
    exact precedingTarget
  have suffixResult := fold_preserves_first curve modulus suffix base target following
    basePoint targetPoint followingBase followingTarget followingAccepted
  rw [repeatedAttemptsStore_fold, order, List.foldl_append]
  exact ⟨suffixResult.2.trans followingSelected, suffixResult.1⟩

/-- Actual fresh allocation supplies the false initial latch for the original first-write rule. -/
theorem repeatedAttemptsStore_initial_selected_first
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (before : Store ctx)
    (basePoint targetPoint : Pure.Point curve)
    (baseRep : PointRepresents curve (before.read base) basePoint)
    (targetRep : PointRepresents curve (before.read target) targetPoint)
    (earlierSamples suffix : List
      (CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2))))
    (chosen : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (order : List.ofFn samples = earlierSamples ++ chosen :: suffix)
    (rejected : ∀ sample ∈ earlierSamples, ¬SampleAccepted curve modulus basePoint targetPoint
      (before.read sample))
    (eligible : SampleAccepted curve modulus basePoint targetPoint (before.read chosen)) :
    let raw := FiniteCyclicDLP.RawRecovery.outputCells modulus
      (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.read chosen))
    let after := repeatedAttemptsStore curve modulus samples base target
      (persistentInitialStore width scalarWidth before)
    after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        raw.second.first ∧
      (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true := by
  have result := repeatedAttemptsStore_selected_first curve modulus samples base target
    (persistentInitialStore width scalarWidth before) basePoint targetPoint
    (by rw [persistentInitialStore_read]; exact baseRep)
    (by rw [persistentInitialStore_read]; exact targetRep)
    earlierSamples suffix chosen order
    (by
      have initial := persistentInitialStore_accepted width scalarWidth before
      exact congrArg CShape.Value.toBool initial)
    (by intro sample member; rw [persistentInitialStore_read]; exact rejected sample member)
    (by rw [persistentInitialStore_read]; exact eligible)
  simpa only [persistentInitialStore_read] using result

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
