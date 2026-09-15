/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add.Semantics
import all QuantumAlg.Components.Classical.ConstantWord.Store

/-!
# Actual original doubling-stage execution

Each original component runs on the actual predecessor Store and contributes
its own native path. The complete quantum reference and prior history are
retained by the same real seven-stage program and its lexical allocation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Each actual prefix instruction or original tail contributes its real full Store and path. -/
def doublingStageRecord (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 7) : Store ctx → Store ctx ×
      (doublingStage spec pointX pointY scratch output index).Path := by
  refine Fin.cases (Field.Native.mulIntoWordStep spec.field pointX pointX scratch.xSquared)
    (fun index => ?_) index
  refine Fin.cases (Field.Native.addIntoWordStep spec.field (classifierRead scratch.xSquared)
    (classifierRead scratch.xSquared) scratch.doubledXSquared) (fun index => ?_) index
  refine Fin.cases (Field.Native.addIntoWordStep spec.field (classifierRead scratch.doubledXSquared)
    (classifierRead scratch.xSquared) scratch.tripledXSquared) (fun index => ?_) index
  refine Fin.cases (ConstantWord.foldStep scratch.a
    (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat)))
    (fun index => ?_) index
  refine Fin.cases (Field.Native.addIntoWordStep spec.field (classifierRead scratch.tripledXSquared)
    (classifierRead scratch.a) scratch.numerator) (fun index => ?_) index
  refine Fin.cases (Field.Native.addIntoWordStep spec.field pointY pointY scratch.denominator)
    (fun index => ?_) index
  refine Fin.cases (affineIntoStep spec.field pointX pointX pointY
    (classifierRead scratch.numerator)
    (classifierRead scratch.denominator) output) (fun index => ?_) index
  exact Fin.elim0 index

/-- Every actual stage preserves the complete quantum-reference block and original history. -/
theorem doublingStage_execute (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 7) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (doublingStage spec pointX pointY scratch output index).execute Reference state =
      state.mapClassical (fun entry =>
        ((doublingStageRecord spec pointX pointY scratch output index entry.1).1,
          (entry.2, (doublingStageRecord spec pointX pointY scratch output index entry.1).2))) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact ConstantWord.constantWord_fold_execute _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.addIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact affineInto_execute _ _ _ _ _ _ _ Reference state
  exact Fin.elim0 index

/-- Actual chronological Store and native paths of the complete original doubling body. -/
def doublingBodyStep (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (doublingBody spec pointX pointY scratch output).Path :=
  Circuit.forRangeRecord 7 (doublingStage spec pointX pointY scratch output)
    (doublingStageRecord spec pointX pointY scratch output)

/-- The actual original seven-call sequence follows that same complete execution record. -/
theorem doublingBody_execute (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (doublingBody spec pointX pointY scratch output).execute Reference state =
      state.mapClassical (fun entry =>
        ((doublingBodyStep spec pointX pointY scratch output entry.1).1,
          (entry.2, (doublingBodyStep spec pointX pointY scratch output entry.1).2))) :=
  Circuit.execute_forRangeRecord 7 (doublingStage spec pointX pointY scratch output)
    (doublingStageRecord spec pointX pointY scratch output)
    (doublingStage_execute spec pointX pointY scratch output) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
