/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Recovery.Semantics
import all QuantumAlg.Components.Classical.FirstAccepted.Placement.Semantics

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
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The original selector consumes the real recovery and verification store. -/
noncomputable def attemptRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx × model.HiddenState) :
      (Store ctx × model.HiddenState) ×
        (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected).Path :=
  let recovered := Classical.choose
    (recoveryInto_actualRecord (environment := environment) curve modulus sample base target
      inverseSuccess candidate
      reconstruction scalarResult targetAccepted)
  let selection := Classical.choose
    (FirstAccepted.withSelection_actualRecord (environment := environment)
      ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected)
  Circuit.sequenceRecord _ _ recovered selection before

/-- The actual six-stage caller store after conditional selection. -/
def attemptStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx × model.HiddenState) : Store ctx :=
  (attemptRecord (environment := environment) curve modulus sample base target inverseSuccess
    candidate reconstruction
    scalarResult targetAccepted accepted selected before).1.1

/-- Conditional selection consumes the caller store returned by the exact recovery record. -/
lemma attemptStore_eq (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (before : Store ctx × model.HiddenState) :
    attemptStore (environment := environment) curve modulus sample base target inverseSuccess
      candidate reconstruction
      scalarResult targetAccepted accepted selected before =
        FirstAccepted.selectionWrite
          ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩
          accepted selected
          (recoveryStore (environment := environment) curve modulus sample base target
            inverseSuccess candidate reconstruction
            scalarResult targetAccepted before) := by
  let recoveryResult := recoveryInto_actualRecord (environment := environment) curve modulus
    sample base target
    inverseSuccess candidate reconstruction scalarResult targetAccepted
  let selectionResult := FirstAccepted.withSelection_actualRecord (environment := environment)
    ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected
  have recoveryStored := (Classical.choose_spec recoveryResult).2 before
  have selectionStored := (Classical.choose_spec selectionResult).2
    ((Classical.choose recoveryResult) before).1
  unfold attemptStore attemptRecord
  rw [Circuit.sequenceRecord_store, selectionStored, recoveryStored]

/-- One actual record preserves the original six stages, their complete store and actual paths. -/
lemma attemptInto_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (targetAccepted : CWriteRef ctx .bit)
    (accepted : CWriteRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord scalarWidth)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected).execute environment Reference state =
            state.mapClassical (fun entry =>
              let result := record (entry.1, entry.2.1)
              (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        attemptStore (environment := environment) curve modulus sample base target
          inverseSuccess candidate reconstruction
          scalarResult targetAccepted accepted selected before := by
  let recoveryResult := recoveryInto_actualRecord (environment := environment) curve modulus
    sample base target
    inverseSuccess candidate reconstruction scalarResult targetAccepted
  let selectionResult := FirstAccepted.withSelection_actualRecord (environment := environment)
      ⟨.storage targetAccepted.toCStorageRef, .storage candidate.toCStorageRef⟩ accepted selected
  refine ⟨attemptRecord (environment := environment) curve modulus sample base target
    inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected, ?_, ?_⟩
  · intro Reference History _ state
    exact Circuit.execute_sequenceRecord (environment := environment) _ _ (Classical.choose
      recoveryResult)
      (Classical.choose selectionResult) (Classical.choose_spec recoveryResult).1
      (Classical.choose_spec selectionResult).1 Reference state
  · intro before
    rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
