/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Observation

/-!
# The original first accepted value survives later actual attempts

Once acceptance is true, the original selector leaves the selected word
unchanged. This fact holds for every stored sample and point encoding; it
does not depend on a successful recovery or a probability assumption.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- An already accepted first value is retained for arbitrary subsequent actual recovery inputs. -/
theorem persistentAttemptStore_preserves_first_of_accepted
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth))
    (already : (before.read (.storage
      (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true) :
    let after := persistentAttemptStore curve modulus sample base target before
    (after.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ∧
      after.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        before.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) := by
  have latches := attempt_latches curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth) before (attemptKeys_distinct ctx width scalarWidth)
  dsimp only at latches ⊢
  simpa only [persistentAttemptStore, already, Bool.true_or, Bool.not_true, Bool.false_and,
    Bool.false_eq_true,
    if_false] using latches

private def firstSelected (width scalarWidth : Nat)
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (store : Store (persistentCtx ctx width scalarWidth)) : Prop :=
  (store.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ∧
    store.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted

private def PreservesStore (code : Circuit ctx ctx) (predicate : Store ctx → Prop) : Prop :=
  ∀ {Reference : Register} {H : Type} [Fintype H] (state : State ctx Reference H),
    (∀ entry, 0 < (state.block entry).mass → predicate entry.1) →
      ∀ result, 0 < ((code.execute Reference state).block result).mass → predicate result.1

private theorem preservesStore_seq (first second : Circuit ctx ctx) (predicate : Store ctx → Prop)
    (firstKeeps : PreservesStore first predicate) (secondKeeps : PreservesStore second predicate) :
    PreservesStore (first.seq second) predicate := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := secondKeeps (first.execute Reference state) (firstKeeps state holds) original present
  rw [← equality]
  exact kept

private theorem persistentAttempt_supported_first
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (wanted : (CShape.unsignedWord scalarWidth).Value) :
    PreservesStore (persistentAttempt curve modulus sample base target)
      (firstSelected width scalarWidth wanted) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
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
  have input := holds original present
  have kept := persistentAttemptStore_preserves_first_of_accepted curve modulus sample base target
    original.1 input.1
  rw [← equality]
  dsimp only
  rw [stores]
  exact ⟨kept.1, kept.2.trans input.2⟩

private theorem sampled_supported_first
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (width scalarWidth : Nat)
    (wanted : (CShape.unsignedWord scalarWidth).Value) :
    PreservesStore (underPersistent sampleCode supported width scalarWidth)
      (firstSelected width scalarWidth wanted) := by
  unfold PreservesStore
  intro Reference H _ state holds result positive
  have paired : ∀ entry, 0 < (state.block entry).mass →
      ((entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool,
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef)) =
          (true, wanted) := by
    intro entry present
    exact Prod.ext (holds entry present).1 (holds entry present).2
  have kept := underPersistent_latches_supported sampleCode supported width scalarWidth state
    (true, wanted) paired result positive
  exact ⟨congrArg Prod.fst kept, congrArg Prod.snd kept⟩

/-- Actual sampling followed by checked recovery preserves an already accepted first word. -/
theorem sampledAttempt_preserves_first
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) {Reference : Register}
    {H : Type} [Fintype H] (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (wanted : (CShape.unsignedWord scalarWidth).Value)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
          true ∧
        entry.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) = wanted)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (sampledAttempt sampleCode supported curve modulus sample base target).Path))
    (positive : 0 < (((sampledAttempt sampleCode supported curve modulus sample base
      target).execute
      Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        true ∧
      result.1.read (.storage (persistentSelected ctx width scalarWidth).toCStorageRef) =
        wanted := by
  exact @preservesStore_seq kind (persistentCtx ctx width scalarWidth)
    (underPersistent sampleCode supported width scalarWidth)
    (persistentAttempt curve modulus sample base target) (firstSelected width scalarWidth wanted)
    (@sampled_supported_first kind ctx sampleCode supported width scalarWidth wanted)
    (@persistentAttempt_supported_first kind ctx width scalarWidth curve modulus sample base target
      wanted) Reference H _ state holds result positive

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
