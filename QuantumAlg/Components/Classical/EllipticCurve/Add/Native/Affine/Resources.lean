/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Mul.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Original resources of the actual common affine tail

Each of the nine original calls retains its own event and duration allowance:
one total coefficient computation, three products, four subtractions and one
nominal adapter. The eight arithmetic words and initialized false tag remain
live across the largest active arithmetic scope. Durations are also tied
exactly to the event trace of the same actual execution path.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular Field.Native

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Distinct original native allowances in their actual chronological positions. -/
def affineStageEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : Fin 9 → ResourcePool model :=
  let product := ResourcePool.ofList (multiplicationTrace model spec)
  let subtraction := ResourcePool.ofList (subtractionTrace model spec)
  ![coefficientEnvelope model spec, product, product, subtraction, subtraction,
    subtraction, product, subtraction,
    ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packEllipticCurvePoint width)))]]

/-- The original nine distinct allowances are added, with every loader counted at each call. -/
def affineEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : ResourcePool model :=
  ∑ index, affineStageEnvelope model spec index

/-- Original stage duration allowances retain each real field-constant loader. -/
def affineStageDepthLimit {model : ExecutionModel} [BitWord.Selected model]
    (spec : ModulusSpec width) (duration : Resource.Event model → Nat) :
    Fin 9 → Nat :=
  let product := ((multiplicationTrace model spec).map duration).sum
  let subtraction := ((subtractionTrace model spec).map duration).sum
  ![coefficientDepthLimit spec duration, product, product, subtraction, subtraction,
    subtraction, product, subtraction,
    duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packEllipticCurvePoint width))))]

/-- The original serial dependency allowance adds the nine actual calls. -/
def affineDepthLimit {model : ExecutionModel} [BitWord.Selected model]
    (spec : ModulusSpec width) (duration : Resource.Event model → Nat) : Nat :=
  ∑ index, affineStageDepthLimit spec duration index

/-- Only one of the original arithmetic scopes is active at a time. -/
def affineActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (((coefficientShapes width).map SpacePool.ofShape).sum +
    coefficientActiveSpace kind width)
    (SpacePool.max (multiplicationScratchSpace kind width)
      (((subtractionShapes width).map SpacePool.ofShape).sum +
        subtractionReductionSpace kind width))

section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

private lemma affineStage_pool_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 9)
    (path : (affineStage spec leftX rightX leftY numerator denominator scratch output index).Path) :
    (affineStage spec leftX rightX leftY numerator denominator scratch output index).resourcePool
      path ≤
      affineStageEnvelope model spec index := by
  revert path
  fin_cases index <;> intro path
  all_goals first
    | exact coefficientIntoWord_pool_le _ _ _ path
    | exact (mulIntoWord_resourcePool _ _ _ _ path).le
    | exact (subIntoWord_resourcePool _ _ _ _ path).le
    | exact (congrArg ResourcePool.ofList (repackRawInto_eventTrace _ _ path)).le

private lemma affineBody_pool_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (affineBody spec leftX rightX leftY numerator denominator scratch output).Path) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).resourcePool path ≤
      affineEnvelope model spec :=
  Circuit.forRange_pool_le_sum 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    (affineStageEnvelope model spec)
    (affineStage_pool_le spec leftX rightX leftY numerator denominator scratch output) path

private lemma affineStage_depth_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (index : Fin 9)
    (path : (affineStage spec leftX rightX leftY numerator denominator scratch output index).Path) :
    (affineStage spec leftX rightX leftY numerator denominator scratch output index).depth
      duration path ≤
      affineStageDepthLimit spec duration index := by
  revert path
  fin_cases index <;> intro path
  all_goals first
    | exact coefficientIntoWord_depth_le _ _ _ duration path
    | exact (mulIntoWord_durationDepth _ _ _ _ duration path).le
    | exact (subIntoWord_durationDepth _ _ _ _ duration path).le
    | exact (repackRawInto_depth _ _ duration path).le

private lemma affineBody_depth_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (affineBody spec leftX rightX leftY numerator denominator scratch output).Path) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).depth duration path ≤
      affineDepthLimit spec duration :=
  Circuit.forRange_depth_le_sum 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    duration (affineStageDepthLimit spec duration)
    (affineStage_depth_le spec leftX rightX leftY numerator denominator scratch output
      duration) path

private lemma affineStage_duration_eventTrace (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (index : Fin 9)
    (path : (affineStage spec leftX rightX leftY numerator denominator scratch output index).Path) :
    (affineStage spec leftX rightX leftY numerator denominator scratch output index).depth
      duration path =
      ((((affineStage spec leftX rightX leftY numerator denominator scratch output
          index).eventTrace
        path).map duration).sum) := by
  revert path
  fin_cases index <;> intro path
  all_goals first
    | exact coefficientIntoWord_duration_eventTrace _ _ _ duration path
    | exact (mulIntoWord_durationDepth _ _ _ _ duration path).trans
        (congrArg (fun events => (events.map duration).sum)
          (fieldMulIntoWord_eventTrace _ _ _ _ path).symm)
    | exact (subIntoWord_durationDepth _ _ _ _ duration path).trans
        (congrArg (fun events => (events.map duration).sum)
          (fieldSubIntoWord_eventTrace _ _ _ _ path).symm)
    | exact (Nat.add_zero _).symm

private lemma affineBody_duration_eventTrace (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (affineBody spec leftX rightX leftY numerator denominator scratch output).Path) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).depth duration path =
      ((((affineBody spec leftX rightX leftY numerator denominator scratch output).eventTrace
        path).map duration).sum) :=
  Circuit.forRange_duration_eventTrace 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output) duration
    (affineStage_duration_eventTrace spec leftX rightX leftY numerator denominator scratch output
      duration) path

/-- The actual nine-call native ledger satisfies the original distinct-stage allowance. -/
lemma affineInto_pool_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (affineInto spec leftX rightX leftY numerator denominator output).Path) :
    (affineInto spec leftX rightX leftY numerator denominator output).resourcePool path ≤
      affineEnvelope model spec := by
  exact withCellsFrom_property (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.resourcePool selected ≤ affineEnvelope model spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => affineBody_pool_le _ _ _ _ _ _ _ _ selected) path

/-- Every actual path satisfies the original serial duration allowance. -/
lemma affineInto_depth_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (affineInto spec leftX rightX leftY numerator denominator output).Path) :
    (affineInto spec leftX rightX leftY numerator denominator output).depth duration path ≤
      affineDepthLimit spec duration := by
  exact withCellsFrom_property (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected ≤ affineDepthLimit spec duration)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => affineBody_depth_le _ _ _ _ _ _ _ _ duration selected) path

/-- Actual selected durations equal the same complete original native event trace. -/
lemma affineInto_duration_eventTrace (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (affineInto spec leftX rightX leftY numerator denominator output).Path) :
    (affineInto spec leftX rightX leftY numerator denominator output).depth duration path =
      (((affineInto spec leftX rightX leftY numerator denominator output).eventTrace path).map
        duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      affineBody_duration_eventTrace _ _ _ _ _ _ _ _ duration selected) path

private lemma affineBody_resident_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (affineBody spec leftX rightX leftY numerator denominator scratch output).Path) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).peakResidentSpace
      path ≤
      affineActiveSpace model.kind width + ctx.residentSpace := by
  refine Circuit.forRange_resident_le 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    (affineActiveSpace model.kind width + ctx.residentSpace) le_add_self ?_ path
  intro index selected
  revert selected
  fin_cases index <;> intro selected
  all_goals first
    | exact (coefficientIntoWord_resident_le _ _ _ selected).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    | exact (mulIntoWord_resident _ _ _ _ selected).le.trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (subIntoWord_resident _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (repackRawInto_resident _ _ selected).le.trans le_add_self

/-- All original persistent tail cells coexist with the largest active arithmetic scope. -/
lemma affineInto_resident_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (affineInto spec leftX rightX leftY numerator denominator output).Path) :
    (affineInto spec leftX rightX leftY numerator denominator output).peakResidentSpace
      path ≤
      ((affineShapes width).map SpacePool.ofShape).sum + affineActiveSpace model.kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (affineActiveSpace model.kind width)
    (fun cells _ transport _ selected => affineBody_resident_le _ _ _ _ _ _ _ _ selected) path

private lemma affineBody_auxiliary_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (scratch : AffineScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (affineBody spec leftX rightX leftY numerator denominator scratch output).Path) :
    (affineBody spec leftX rightX leftY numerator denominator scratch output).peakAuxiliarySpace
      path ≤
      affineActiveSpace model.kind width + ctx.auxiliarySpace := by
  refine Circuit.forRange_auxiliary_le 9
    (affineStage spec leftX rightX leftY numerator denominator scratch output)
    (affineActiveSpace model.kind width + ctx.auxiliarySpace) le_add_self ?_ path
  intro index selected
  revert selected
  fin_cases index <;> intro selected
  all_goals first
    | exact (coefficientIntoWord_auxiliary_le _ _ _ selected).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    | exact (mulIntoWord_auxiliary _ _ _ _ selected).le.trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (subIntoWord_auxiliary _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (repackRawInto_auxiliary _ _ selected).le.trans le_add_self

/-- All original persistent tail cells coexist with the largest active arithmetic scope. -/
lemma affineInto_auxiliary_le (spec : ModulusSpec width)
    (leftX rightX leftY numerator denominator : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (affineInto spec leftX rightX leftY numerator denominator output).Path) :
    (affineInto spec leftX rightX leftY numerator denominator output).peakAuxiliarySpace
      path ≤
      ((affineShapes width).map SpacePool.ofShape).sum + affineActiveSpace model.kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (affineShapes width)
    (fun cells _ transport _ => affineBody spec (transport.liftInput leftX)
      (transport.liftInput rightX) (transport.liftInput leftY) (transport.liftInput numerator)
      (transport.liftInput denominator) (affineScratch cells) (transport.liftWrite output))
    (affineActiveSpace model.kind width)
    (fun cells _ transport _ selected => affineBody_auxiliary_le _ _ _ _ _ _ _ _ selected) path

end

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
