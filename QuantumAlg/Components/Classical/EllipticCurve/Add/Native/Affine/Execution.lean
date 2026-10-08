/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Record

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

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Each original stage returns its own certified actual complete Store and native path. -/
def affineStageRecord (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (affineStage (model := model) spec leftX rightX leftY numerator denominator scratch output
        index).Path := by
  refine Fin.cases (Field.Native.coefficientIntoWordStep spec denominator scratch.coefficient)
    (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.mulIntoWordStep spec numerator
      (classifierRead scratch.coefficient) scratch.slope before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.mulIntoWordStep spec (classifierRead scratch.slope)
      (classifierRead scratch.slope) scratch.slopeSquared before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.subIntoWordStep spec (classifierRead scratch.slopeSquared)
      leftX scratch.xPartial before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.subIntoWordStep spec (classifierRead scratch.xPartial)
      rightX scratch.xOutput before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.subIntoWordStep spec leftX (classifierRead scratch.xOutput)
      scratch.xDifference before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.mulIntoWordStep spec (classifierRead scratch.slope)
      (classifierRead scratch.xDifference) scratch.yProduct before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let result := Field.Native.subIntoWordStep spec (classifierRead scratch.yProduct)
      leftY scratch.yOutput before.1
    ((result.1, before.2), result.2)) (fun index => ?_) index
  refine Fin.cases (fun before =>
    let raw : CInputRef ctx (PointEquality.RawPointShape width) :=
      .product (classifierRead scratch.tag)
      (.product (classifierRead scratch.xOutput) (classifierRead scratch.yOutput))
    ((repackStore raw output before.1, before.2),
      (BitWord.instructionStep (execution := model) (repackOp raw output) before.1).2))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- Actual stages retain every complete quantum-reference block and original history. -/
theorem affineStage_execute (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (affineStage (model := model) spec leftX rightX leftY numerator denominator scratch output
      index).execute
      Reference state = state.mapClassical (fun entry =>
        let result := affineStageRecord spec leftX rightX leftY numerator denominator scratch output
          index (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.coefficientIntoWord_execute _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.mulIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact Field.Native.subIntoWord_execute _ _ _ _ Reference state
  refine Fin.cases ?_ (fun index => ?_) index
  · dsimp only [affineStage, affineStageRecord]
    exact repackRawInto_execute _ _ Reference state
  exact Fin.elim0 index

/-- Actual predecessor stores are threaded through the entire original nine-stage tail. -/
def affineBodyStep (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width)) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (affineBody (model := model) spec leftX rightX leftY numerator denominator scratch
        output).Path :=
  Circuit.forRangeRecord 9
    (affineStage (model := model) spec leftX rightX leftY numerator denominator scratch output)
    (affineStageRecord spec leftX rightX leftY numerator denominator scratch output)

/-- Full actual tail execution follows the same certified sequential store record. -/
theorem affineBody_execute (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (affineBody (model := model) spec leftX rightX leftY numerator denominator scratch
      output).execute
      Reference state = state.mapClassical (fun entry =>
        let result := affineBodyStep spec leftX rightX leftY numerator denominator scratch output
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) :=
  Circuit.execute_forRangeRecord 9
    (affineStage (model := model) spec leftX rightX leftY numerator denominator scratch output)
    (affineStageRecord spec leftX rightX leftY numerator denominator scratch output)
    (affineStage_execute spec leftX rightX leftY numerator denominator scratch output)
      Reference state

/-- Every actual allocation and release participates in the complete original affine execution. -/
theorem affineInto_actualRecord (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
        (affineInto (model := model) spec leftX rightX leftY numerator denominator output).Path,
      ∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (affineInto (model := model) spec leftX rightX leftY numerator denominator output).execute
          Reference state = state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  apply withCellsFrom_hasRecord (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody (model := model) spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
  intro inner cells distinct transport separated
  exact ⟨affineBodyStep spec (transport.liftInput leftX) (transport.liftInput rightX)
    (transport.liftInput leftY) (transport.liftInput numerator) (transport.liftInput denominator)
    (affineScratch cells) (transport.liftWrite output), affineBody_execute _ _ _ _ _ _ _ _⟩

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
