/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Semantics

/-!
# Complete actual execution of the original common affine tail

Each original component consumes the actual Store returned by its predecessor.
Their existing full-state records compose through the native nine-stage tail
and its lexical allocations. This execution bridge alone does not assert a
field-inverse condition or the mathematical point-addition formula.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Each original stage returns its own certified actual complete Store and native path. -/
def affineStageRecord (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9) :
    Store ctx → Store ctx ×
      (affineStage spec leftX rightX leftY numerator denominator scratch output index).Path := by
  refine Fin.cases (Field.Native.coefficientIntoWordStep spec denominator scratch.coefficient)
    (fun index => ?_) index
  refine Fin.cases (Field.Native.mulIntoWordStep spec numerator
    (classifierRead scratch.coefficient) scratch.slope) (fun index => ?_) index
  refine Fin.cases (Field.Native.mulIntoWordStep spec (classifierRead scratch.slope)
    (classifierRead scratch.slope) scratch.slopeSquared) (fun index => ?_) index
  refine Fin.cases (Field.Native.subIntoWordStep spec (classifierRead scratch.slopeSquared)
    leftX scratch.xPartial) (fun index => ?_) index
  refine Fin.cases (Field.Native.subIntoWordStep spec (classifierRead scratch.xPartial)
    rightX scratch.xOutput) (fun index => ?_) index
  refine Fin.cases (Field.Native.subIntoWordStep spec leftX (classifierRead scratch.xOutput)
    scratch.xDifference) (fun index => ?_) index
  refine Fin.cases (Field.Native.mulIntoWordStep spec (classifierRead scratch.slope)
    (classifierRead scratch.xDifference) scratch.yProduct) (fun index => ?_) index
  refine Fin.cases (Field.Native.subIntoWordStep spec (classifierRead scratch.yProduct)
    leftY scratch.yOutput) (fun index => ?_) index
  refine Fin.cases (fun store => (repackStore (.product (classifierRead scratch.tag)
    (.product (classifierRead scratch.xOutput) (classifierRead scratch.yOutput))) output store, ()))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- Actual stages retain every complete quantum-reference block and original history. -/
theorem affineStage_execute (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (affineStage spec leftX rightX leftY numerator denominator scratch output index).execute
      Reference state = state.mapClassical (fun entry =>
        ((affineStageRecord spec leftX rightX leftY numerator denominator scratch output
          index entry.1).1,
          (entry.2, (affineStageRecord spec leftX rightX leftY numerator denominator scratch output
            index entry.1).2))) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.coefficientIntoWord_execute _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · refine (repackRawInto_execute _ _ Reference state).trans ?_
    congr 1
    exact Subsingleton.elim _ _
  exact Fin.elim0 index

/-- Actual predecessor stores are threaded through the entire original nine-stage tail. -/
def affineBodyStep (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx ×
      (affineBody spec leftX rightX leftY numerator denominator scratch output).Path :=
  Circuit.forRangeRecord 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    (affineStageRecord spec leftX rightX leftY numerator denominator scratch output)

/-- Full actual tail execution follows the same certified sequential store record. -/
theorem affineBody_execute (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).execute
      Reference state = state.mapClassical (fun entry =>
        ((affineBodyStep spec leftX rightX leftY numerator denominator scratch output entry.1).1,
          (entry.2,
            (affineBodyStep spec leftX rightX leftY numerator denominator scratch output
              entry.1).2))) :=
  Circuit.execute_forRangeRecord 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    (affineStageRecord spec leftX rightX leftY numerator denominator scratch output)
    (affineStage_execute spec leftX rightX leftY numerator denominator scratch output)
      Reference state

/-- Every actual allocation and release participates in the complete original affine execution. -/
theorem affineInto_actualRecord (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx → Store ctx ×
        (affineInto spec leftX rightX leftY numerator denominator output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (affineInto spec leftX rightX leftY numerator denominator output).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))) := by
  apply withCellsFrom_property (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (fun {inner} _ code => ∃ record : Store inner → Store inner × code.Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State inner Reference History), code.execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2))))
  · intro inner transport key shape fresh body available
    obtain ⟨record, equation⟩ := available
    exact ⟨Circuit.workspaceRecord key shape fresh body record,
      Circuit.execute_workspaceRecord key shape fresh body record equation⟩
  · intro inner cells distinct transport separated
    exact ⟨affineBodyStep spec (transport.liftInput leftX) (transport.liftInput rightX)
      (transport.liftInput leftY) (transport.liftInput numerator) (transport.liftInput denominator)
      (affineScratch cells) (transport.liftWrite output), affineBody_execute _ _ _ _ _ _ _ _⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
