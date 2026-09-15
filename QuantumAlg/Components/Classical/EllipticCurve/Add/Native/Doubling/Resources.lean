/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Doubling
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add.Resources

/-!
# Original resources of the actual finite doubling arm

The original square, four field additions and actual public coefficient load
precede the complete affine tail. Every stage retains its own serial allowance.
The six persistent prefix words coexist with the largest actual nested scope.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular Field.Native
open ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original coefficient loader is charged for its actual public word bits. -/
def doublingLoaderTrace (kind : ProblemKind) (spec : CurveSpec width) :
    List (Resource.Event kind) :=
  ConstantWord.loaderTrace kind width
    (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat))

/-- Original native allowances in the seven actual chronological positions. -/
def doublingStageEnvelope (kind : ProblemKind) (spec : CurveSpec width) :
    Fin 7 → ResourcePool kind :=
  let addition := ResourcePool.ofList (additionTrace kind spec.field)
  ![ResourcePool.ofList (multiplicationTrace kind spec.field), addition, addition,
    ResourcePool.ofList (doublingLoaderTrace kind spec), addition, addition,
    affineEnvelope kind spec.field]

/-- Each original multiplication, addition, public loader and tail is charged exactly once. -/
def doublingEnvelope (kind : ProblemKind) (spec : CurveSpec width) : ResourcePool kind :=
  ∑ index, doublingStageEnvelope kind spec index

/-- Original native-duration allowances in their seven actual chronological positions. -/
def doublingStageDepthLimit (spec : CurveSpec width) (duration : Resource.Event kind → Nat) :
    Fin 7 → Nat :=
  let addition := ((additionTrace kind spec.field).map duration).sum
  ![((multiplicationTrace kind spec.field).map duration).sum, addition, addition,
    ((doublingLoaderTrace kind spec).map duration).sum, addition, addition,
    affineDepthLimit spec.field duration]

/-- The original serial allowance retains every real public-constant loader duration. -/
def doublingDepthLimit (spec : CurveSpec width) (duration : Resource.Event kind → Nat) : Nat :=
  ∑ index, doublingStageDepthLimit spec duration index

/-- Prefix arithmetic and the complete affine tail occupy successive actual scopes. -/
def doublingActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (multiplicationScratchSpace kind width)
    (SpacePool.max (((additionShapes width).map SpacePool.ofShape).sum +
      additionReductionSpace kind width)
      (((affineShapes width).map SpacePool.ofShape).sum + affineActiveSpace kind width))

private theorem doublingStage_pool_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (index : Fin 7)
    (path : (doublingStage spec pointX pointY scratch output index).Path) :
    (doublingStage spec pointX pointY scratch output index).resourcePool
      path ≤
      doublingStageEnvelope kind spec index := by
  fin_cases index
  all_goals first
    | exact (mulIntoWord_resourcePool _ _ _ _ path).le
    | exact (addIntoWord_resourcePool _ _ _ _ path).le
    | exact (congrArg ResourcePool.ofList (ConstantWord.constantFold_eventTrace scratch.a
        (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat)) path)).le
    | exact affineInto_pool_le _ _ _ _ _ _ _ path

private theorem doublingBody_pool_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (doublingBody spec pointX pointY scratch output).Path) :
    (doublingBody spec pointX pointY scratch output).resourcePool path ≤
      doublingEnvelope kind spec :=
  Circuit.forRange_pool_le_sum 7
    (doublingStage spec pointX pointY scratch output)
    (doublingStageEnvelope kind spec)
    (doublingStage_pool_le spec pointX pointY scratch output) path

private theorem doublingStage_depth_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (index : Fin 7)
    (path : (doublingStage spec pointX pointY scratch output index).Path) :
    (doublingStage spec pointX pointY scratch output index).depth
      duration path ≤
      doublingStageDepthLimit spec duration index := by
  fin_cases index
  all_goals first
    | exact (mulIntoWord_durationDepth _ _ _ _ duration path).le
    | exact (addIntoWord_durationDepth _ _ _ _ duration path).le
    | exact (ConstantWord.constantFold_depth scratch.a
        (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat))
        duration path).le
    | exact affineInto_depth_le _ _ _ _ _ _ _ duration path

private theorem doublingBody_depth_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (doublingBody spec pointX pointY scratch output).Path) :
    (doublingBody spec pointX pointY scratch output).depth duration path ≤
      doublingDepthLimit spec duration :=
  Circuit.forRange_depth_le_sum 7
    (doublingStage spec pointX pointY scratch output)
    duration (doublingStageDepthLimit spec duration)
    (doublingStage_depth_le spec pointX pointY scratch output
      duration) path

private theorem doublingStage_duration_eventTrace (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (index : Fin 7)
    (path : (doublingStage spec pointX pointY scratch output index).Path) :
    (doublingStage spec pointX pointY scratch output index).depth
      duration path =
      ((((doublingStage spec pointX pointY scratch output
          index).eventTrace
        path).map duration).sum) := by
  fin_cases index
  all_goals first
    | exact (mulIntoWord_durationDepth _ _ _ _ duration path).trans
        (congrArg (fun events => (events.map duration).sum)
          (fieldMulIntoWord_eventTrace _ _ _ _ path).symm)
    | exact (addIntoWord_durationDepth _ _ _ _ duration path).trans
        (congrArg (fun events => (events.map duration).sum)
          (fieldAddIntoWord_eventTrace _ _ _ _ path).symm)
    | exact (ConstantWord.constantFold_depth scratch.a
        (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat))
        duration path).trans (congrArg (fun events => (events.map duration).sum)
          (ConstantWord.constantFold_eventTrace scratch.a
            (List.ofFn (ConstantWord.constantBits width (doublingCurveAWord spec).toNat))
            path).symm)
    | exact affineInto_duration_eventTrace _ _ _ _ _ _ _ duration path

private theorem doublingBody_duration_eventTrace (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (doublingBody spec pointX pointY scratch output).Path) :
    (doublingBody spec pointX pointY scratch output).depth duration path =
      ((((doublingBody spec pointX pointY scratch output).eventTrace
        path).map duration).sum) :=
  Circuit.forRange_duration_eventTrace 7
    (doublingStage spec pointX pointY scratch output) duration
    (doublingStage_duration_eventTrace spec pointX pointY scratch output
      duration) path

/-- The actual seven-call native ledger satisfies the original distinct-stage allowance. -/
theorem doublingInto_pool_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (doublingInto spec point output).Path) :
    (doublingInto spec point output).resourcePool path ≤
      doublingEnvelope kind spec := by
  exact withCellsFrom_property (Transport.id ctx) (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (.first (.second (transport.liftInput point)))
      (.second (.second (transport.liftInput point)))
      (doublingScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.resourcePool selected ≤ doublingEnvelope kind spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => doublingBody_pool_le _ _ _ _ _ selected) path

/-- Every actual path satisfies the original serial duration allowance. -/
theorem doublingInto_depth_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (doublingInto spec point output).Path) :
    (doublingInto spec point output).depth duration path ≤
      doublingDepthLimit spec duration := by
  exact withCellsFrom_property (Transport.id ctx) (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (.first (.second (transport.liftInput point)))
      (.second (.second (transport.liftInput point)))
      (doublingScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected ≤ doublingDepthLimit spec duration)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => doublingBody_depth_le _ _ _ _ _ duration selected) path

/-- Actual selected durations equal the same complete original native event trace. -/
theorem doublingInto_duration_eventTrace (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat)
    (path : (doublingInto spec point output).Path) :
    (doublingInto spec point output).depth duration path =
      (((doublingInto spec point output).eventTrace path).map
        duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (.first (.second (transport.liftInput point)))
      (.second (.second (transport.liftInput point)))
      (doublingScratch cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      doublingBody_duration_eventTrace _ _ _ _ _ duration selected) path

private theorem doublingBody_resident_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (doublingBody spec pointX pointY scratch output).Path) :
    (doublingBody spec pointX pointY scratch output).peakResidentSpace
      path ≤
      doublingActiveSpace kind width + ctx.residentSpace := by
  refine Circuit.forRange_resident_le 7
    (doublingStage spec pointX pointY scratch output)
    (doublingActiveSpace kind width + ctx.residentSpace) le_add_self ?_ path
  intro index selected
  fin_cases index
  all_goals first
    | exact (mulIntoWord_resident _ _ _ _ selected).le.trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    | exact (addIntoWord_resident _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (affineInto_resident_le _ _ _ _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (ConstantWord.constantWord_resident_le _ _ selected).trans le_add_self

/-- All six original persistent prefix cells coexist with the largest active arithmetic scope. -/
theorem doublingInto_resident_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (doublingInto spec point output).Path) :
    (doublingInto spec point output).peakResidentSpace
      path ≤
      ((doublingShapes width).map SpacePool.ofShape).sum + doublingActiveSpace kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (.first (.second (transport.liftInput point)))
      (.second (.second (transport.liftInput point)))
      (doublingScratch cells) (transport.liftWrite output))
    (doublingActiveSpace kind width)
    (fun cells _ transport _ selected => doublingBody_resident_le _ _ _ _ _ selected) path

private theorem doublingBody_auxiliary_le (spec : CurveSpec width)
    (pointX pointY : CInputRef ctx (.unsignedWord width))
    (scratch : DoublingScratch ctx width) (output : CWriteRef ctx (PointShape width))
    (path : (doublingBody spec pointX pointY scratch output).Path) :
    (doublingBody spec pointX pointY scratch output).peakAuxiliarySpace
      path ≤
      doublingActiveSpace kind width + ctx.auxiliarySpace := by
  refine Circuit.forRange_auxiliary_le 7
    (doublingStage spec pointX pointY scratch output)
    (doublingActiveSpace kind width + ctx.auxiliarySpace) le_add_self ?_ path
  intro index selected
  fin_cases index
  all_goals first
    | exact (mulIntoWord_auxiliary _ _ _ _ selected).le.trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    | exact (addIntoWord_auxiliary _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_left _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (affineInto_auxiliary_le _ _ _ _ _ _ _ selected).trans
        (add_le_add ((SpacePool.le_max_right _ _).trans (SpacePool.le_max_right _ _)) le_rfl)
    | exact (ConstantWord.constantWord_auxiliary_le _ _ selected).trans le_add_self

/-- All six original persistent prefix cells coexist with the largest active arithmetic scope. -/
theorem doublingInto_auxiliary_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (doublingInto spec point output).Path) :
    (doublingInto spec point output).peakAuxiliarySpace
      path ≤
      ((doublingShapes width).map SpacePool.ofShape).sum + doublingActiveSpace kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (doublingShapes width)
    (fun cells _ transport _ => doublingBody spec
      (.first (.second (transport.liftInput point)))
      (.second (.second (transport.liftInput point)))
      (doublingScratch cells) (transport.liftWrite output))
    (doublingActiveSpace kind width)
    (fun cells _ transport _ selected => doublingBody_auxiliary_le _ _ _ _ _ selected) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
