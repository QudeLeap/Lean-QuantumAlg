/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native
import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native.Semantics

/-!
# Complete actual candidate-verification records

Each original verification stage consumes the Store returned by its actual
predecessor. The same four-stage circuit preserves the complete quantum
reference and prior history. Its mathematical record contains the genuine
scalar path, point-comparison path and both original Boolean instructions.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Every original actual stage returns its complete Store and native execution path. -/
def verificationStageRecord (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (index : Fin 4) : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) ×
        (verificationStage spec candidate base target inverseSuccess reconstruction
          scalarResult accepted index).Path := by
  refine Fin.cases (ScalarMul.Native.scalarStep (environment := environment) spec (candidateBits
    candidate) base scalarResult)
    (fun index => ?_) index
  refine Fin.cases (Circuit.preserveHiddenRecord (PointEquality.Native.compareStep
    (environment := environment)
    (.storage scalarResult.toCStorageRef) target accepted)) (fun index => ?_) index
  refine Fin.cases (Circuit.preserveHiddenRecord (BitWord.instructionStep
    (execution := model) (conjunctionOp inverseSuccess accepted))) (fun index => ?_) index
  refine Fin.cases (Circuit.preserveHiddenRecord (BitWord.instructionStep
    (execution := model) (conjunctionOp reconstruction accepted))) (fun index => ?_) index
  exact Fin.elim0 index

/-- The four original stages preserve every complete quantum-reference block. -/
lemma verificationStage_execute (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (index : Fin 4) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (verificationStage spec candidate base target inverseSuccess reconstruction scalarResult
      accepted index).execute environment Reference state = state.mapClassical (fun entry =>
        let result := verificationStageRecord (environment := environment) spec candidate base
          target inverseSuccess
          reconstruction scalarResult accepted index (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact ScalarMul.Native.scalarInto_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (PointEquality.Native.compareInto_execute _ _ _ Reference state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
      (conjunctionOp inverseSuccess accepted) state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
      (conjunctionOp reconstruction accepted) state).trans ?_
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  exact Fin.elim0 index

/-- Actual chronological record of the original scalar, comparator and two conjunctions. -/
def verifyStep (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) ×
        (verifyInto spec candidate base target inverseSuccess reconstruction
          scalarResult accepted).Path :=
  Circuit.forRangeRecord 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)
    (verificationStageRecord (environment := environment) spec candidate base target
      inverseSuccess reconstruction
      scalarResult accepted)

/-- The same original circuit and actual record retain all reference correlations and history. -/
lemma verifyInto_execute (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (verifyInto spec candidate base target inverseSuccess reconstruction scalarResult
      accepted).execute environment Reference state = state.mapClassical (fun entry =>
        let result := verifyStep (environment := environment) spec candidate base target
          inverseSuccess reconstruction
          scalarResult accepted (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord (environment := environment) 4 _ _
    (verificationStage_execute spec candidate base target inverseSuccess reconstruction
      scalarResult accepted) Reference state

/-- The complete actual caller Store is exactly the original four chronological updates. -/
lemma verifyStep_store (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (entry : Store ctx × model.HiddenState) :
    (verifyStep (environment := environment) spec candidate base target inverseSuccess
      reconstruction
      scalarResult accepted entry).1.1 =
      let scalar := (ScalarMul.Native.scalarStep (environment := environment) spec
        (candidateBits candidate)
        base scalarResult entry).1
      let compared := (PointEquality.Native.compareStep (environment := environment)
        (.storage scalarResult.toCStorageRef) target accepted scalar.1).1
      (compared.applyOp (conjunctionOp inverseSuccess accepted)).applyOp
        (conjunctionOp reconstruction accepted) := rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
