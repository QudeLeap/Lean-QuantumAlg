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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- Every original actual stage returns its complete Store and native execution path. -/
def verificationStageRecord (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (index : Fin 4) : Store ctx → Store ctx ×
      (verificationStage spec candidate base target inverseSuccess reconstruction
        scalarResult accepted index).Path := by
  refine Fin.cases (ScalarMul.Native.scalarStep spec (candidateBits candidate) base scalarResult)
    (fun index => ?_) index
  refine Fin.cases (PointEquality.Native.compareStep
    (.storage scalarResult.toCStorageRef) target accepted) (fun index => ?_) index
  refine Fin.cases (fun store => (store.applyOp (conjunctionOp inverseSuccess accepted), ()))
    (fun index => ?_) index
  refine Fin.cases (fun store => (store.applyOp (conjunctionOp reconstruction accepted), ()))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- The four original stages preserve every complete quantum-reference block. -/
theorem verificationStage_execute (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (index : Fin 4) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (verificationStage spec candidate base target inverseSuccess reconstruction scalarResult
      accepted index).execute Reference state = state.mapClassical (fun entry =>
        ((verificationStageRecord spec candidate base target inverseSuccess reconstruction
          scalarResult accepted index entry.1).1,
          (entry.2, (verificationStageRecord spec candidate base target inverseSuccess
            reconstruction scalarResult accepted index entry.1).2))) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact ScalarMul.Native.scalarInto_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact PointEquality.Native.compareInto_execute _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (Circuit.execute_classical_mapClassical
      (conjunctionOp inverseSuccess accepted) Reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (Circuit.execute_classical_mapClassical
      (conjunctionOp reconstruction accepted) Reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  exact Fin.elim0 index

/-- Actual chronological record of the original scalar, comparator and two conjunctions. -/
def verifyStep (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit) :
    Store ctx → Store ctx ×
      (verifyInto spec candidate base target inverseSuccess reconstruction
        scalarResult accepted).Path :=
  Circuit.forRangeRecord 4
    (verificationStage spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)
    (verificationStageRecord spec candidate base target inverseSuccess reconstruction
      scalarResult accepted)

/-- The same original circuit and actual record retain all reference correlations and history. -/
theorem verifyInto_execute (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (verifyInto spec candidate base target inverseSuccess reconstruction scalarResult
      accepted).execute Reference state = state.mapClassical (fun entry =>
        ((verifyStep spec candidate base target inverseSuccess reconstruction
          scalarResult accepted entry.1).1,
          (entry.2, (verifyStep spec candidate base target inverseSuccess reconstruction
            scalarResult accepted entry.1).2))) :=
  Circuit.execute_forRangeRecord 4 _ _
    (verificationStage_execute spec candidate base target inverseSuccess reconstruction
      scalarResult accepted) Reference state

/-- The complete actual caller Store is exactly the original four chronological updates. -/
theorem verifyStep_store (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (scalarResult : CWriteRef ctx (PointShape width)) (accepted : CWriteRef ctx .bit)
    (store : Store ctx) :
    (verifyStep spec candidate base target inverseSuccess reconstruction
      scalarResult accepted store).1 =
      let scalar := (ScalarMul.Native.scalarStep spec (candidateBits candidate)
        base scalarResult store).1
      let compared := (PointEquality.Native.compareStep
        (.storage scalarResult.toCStorageRef) target accepted scalar).1
      (compared.applyOp (conjunctionOp inverseSuccess accepted)).applyOp
        (conjunctionOp reconstruction accepted) := rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
