/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Semantics
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Semantics
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Complete actual recovery and verification record

The exact three chronological recovery writes feed the real verification
record on the resulting store. The full-state equation follows the original
sequence instruction and preserves every quantum-reference block and prior
history. It holds for all actual caller aliases, including their real overwrite
effects, without a caller initialization, inverse or secret witness.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Actual recovery writes precede the original complete verification store update. -/
noncomputable def recoveryRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
      (Store ctx × model.HiddenState) ×
        (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted).Path :=
  let raw := Classical.choose
    (FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord (environment := environment)
      modulus sample inverseSuccess candidate reconstruction)
  Circuit.sequenceRecord _ _ raw
    (verifyStep (environment := environment) curve (.storage candidate.toCStorageRef) base target
      (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
      scalarResult accepted) before

/-- The caller store produced by the exact five-stage record. -/
def recoveryStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx × model.HiddenState) : Store ctx :=
  (recoveryRecord (environment := environment) curve modulus sample base target inverseSuccess
    candidate reconstruction
    scalarResult accepted before).1.1

/-- Recovery exposes its three actual cells before verification consumes the resulting state. -/
lemma recoveryStore_eq (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (before : Store ctx × model.HiddenState) :
    recoveryStore (environment := environment) curve modulus sample base target inverseSuccess
      candidate reconstruction
      scalarResult accepted before =
      (verifyStep (environment := environment) curve (.storage candidate.toCStorageRef) base target
        (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
        scalarResult accepted
        (FiniteCyclicDLP.RawRecovery.Native.exposureWrite inverseSuccess candidate
          reconstruction before.1
          (FiniteCyclicDLP.RawRecovery.outputCells modulus
            (FiniteCyclicDLP.RawRecovery.Native.preparationInput (before.1.read sample))),
          (Classical.choose
            (FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord (environment :=
              environment)
              modulus sample inverseSuccess candidate reconstruction) before).1.2)).1.1 := by
  have rawStore := (Classical.choose_spec
    (FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord (environment := environment)
      modulus sample inverseSuccess candidate reconstruction)).2 before
  unfold recoveryStore recoveryRecord
  rw [Circuit.sequenceRecord_store]
  apply congrArg (fun entry : Store ctx × model.HiddenState =>
    (verifyStep (environment := environment) curve (.storage candidate.toCStorageRef) base target
      (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
      scalarResult accepted entry).1.1)
  exact Prod.ext rawStore rfl

/-- The original five stages have one full-state record on their genuine intermediate store. -/
lemma recoveryInto_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit)
    (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (recoveryInto curve modulus sample base target inverseSuccess candidate reconstruction
          scalarResult accepted).execute environment Reference state = state.mapClassical (fun
            entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 =
        recoveryStore (environment := environment) curve modulus sample base target
          inverseSuccess candidate reconstruction
          scalarResult accepted before := by
  let rawResult := FiniteCyclicDLP.RawRecovery.Native.singleIntoCells_actualRecord (environment
    := environment)
      modulus sample inverseSuccess candidate reconstruction
  have rawEquation := (Classical.choose_spec rawResult).1
  let rawRecord := Classical.choose rawResult
  let checked := verifyStep (environment := environment) curve (.storage
    candidate.toCStorageRef) base target
    (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
    scalarResult accepted
  refine ⟨recoveryRecord (environment := environment) curve modulus sample base target
    inverseSuccess candidate
      reconstruction scalarResult accepted, ?_, ?_⟩
  · intro Reference History _ state
    exact Circuit.execute_sequenceRecord (environment := environment) _ _ rawRecord checked
      (fun Reference {_History} _ state => by
        rw [rawEquation Reference state]
        apply ExecutionState.executionState_mapClassical_congr_decision
        intro entry
        rfl)
      (verifyInto_execute curve (.storage candidate.toCStorageRef) base target
        (.storage inverseSuccess.toCStorageRef) (.storage reconstruction.toCStorageRef)
        scalarResult accepted) Reference state
  · intro before
    rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
