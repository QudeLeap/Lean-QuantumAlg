/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Generic
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Resources

/-!
# Original resources of the actual generic finite arm

Both original field subtractions precede the common affine tail. Their real
modulus loaders are counted at every call. The two persistent slope operands
coexist with the larger active prefix or complete tail allocation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular Field.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The two actual subtractions precede the original affine allowance. -/
def genericEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : ModulusSpec width) : ResourcePool model :=
  ResourcePool.ofList (subtractionTrace model spec) +
    (ResourcePool.ofList (subtractionTrace model spec) + affineEnvelope model spec)

/-- Every native duration in both original subtractions precedes the original tail allowance. -/
def genericDepthLimit {model : ExecutionModel} [BitWord.Selected model]
    (spec : ModulusSpec width) (duration : Resource.Event model → Nat) : Nat :=
  ((subtractionTrace model spec).map duration).sum +
    (((subtractionTrace model spec).map duration).sum + affineDepthLimit spec duration)

/-- Prefix arithmetic and the complete affine allocation occupy successive real scopes. -/
def genericActiveSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.max (((subtractionShapes width).map SpacePool.ofShape).sum +
    subtractionReductionSpace kind width)
    (((affineShapes width).map SpacePool.ofShape).sum + affineActiveSpace kind width)

private theorem genericBody_pool_le (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericBody spec leftX leftY rightX rightY numerator denominator output).Path) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).resourcePool path ≤
      genericEnvelope model spec := by
  change ResourcePool.ofList
    ((subIntoWord spec rightY leftY numerator).eventTrace path.1 ++
      ((subIntoWord spec rightX leftX denominator).eventTrace path.2.1 ++
        (affineInto spec leftX rightX leftY (classifierRead numerator)
        (classifierRead denominator) output).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add (subIntoWord_resourcePool _ _ _ _ path.1).le
    (add_le_add (subIntoWord_resourcePool _ _ _ _ path.2.1).le
      (affineInto_pool_le _ _ _ _ _ _ _ path.2.2))

private theorem genericBody_depth_le (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (genericBody spec leftX leftY rightX rightY numerator denominator output).Path) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).depth duration path ≤
      genericDepthLimit spec duration :=
  Nat.add_le_add (subIntoWord_durationDepth _ _ _ _ duration path.1).le
    (Nat.add_le_add (subIntoWord_durationDepth _ _ _ _ duration path.2.1).le
      (affineInto_depth_le _ _ _ _ _ _ _ duration path.2.2))

private theorem genericBody_duration_eventTrace (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (genericBody spec leftX leftY rightX rightY numerator denominator output).Path) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).depth duration path =
      (((genericBody spec leftX leftY rightX rightY numerator denominator output).eventTrace
        path).map
        duration).sum := by
  have first := (subIntoWord_durationDepth spec rightY leftY numerator duration path.1).trans
    (congrArg (fun events => (events.map duration).sum)
      (fieldSubIntoWord_eventTrace spec rightY leftY numerator path.1).symm)
  have second := (subIntoWord_durationDepth spec rightX leftX denominator duration path.2.1).trans
    (congrArg (fun events => (events.map duration).sum)
      (fieldSubIntoWord_eventTrace spec rightX leftX denominator path.2.1).symm)
  change _ + (_ + _) = (List.map duration
    ((subIntoWord spec rightY leftY numerator).eventTrace path.1 ++
      ((subIntoWord spec rightX leftX denominator).eventTrace path.2.1 ++
        (affineInto spec leftX rightX leftY (classifierRead numerator)
        (classifierRead denominator) output).eventTrace path.2.2))).sum
  rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
  exact congrArg₂ Nat.add first (congrArg₂ Nat.add second
    (affineInto_duration_eventTrace _ _ _ _ _ _ _ duration path.2.2))

/-- The actual generic native ledger retains both subtractions and the complete affine tail. -/
theorem genericInto_pool_le (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericInto spec left right output).Path) :
    (genericInto spec left right output).resourcePool path ≤
      genericEnvelope model spec := by
  exact withCellsFrom_property (Transport.id ctx) (genericShapes width)
    (fun cells _ transport _ =>
      genericBody spec (.first (.second (transport.liftInput left)))
        (.second (.second (transport.liftInput left)))
        (.first (.second (transport.liftInput right)))
        (.second (.second (transport.liftInput right))) cells.tail.head.ref cells.head.ref
        (transport.liftWrite output))
    (fun _ code => ∀ selected, code.resourcePool selected ≤ genericEnvelope model spec)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      genericBody_pool_le _ _ _ _ _ _ _ _ selected) path

/-- Every actual generic path satisfies the original serial duration allowance. -/
theorem genericInto_depth_le (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (genericInto spec left right output).Path) :
    (genericInto spec left right output).depth duration path ≤
      genericDepthLimit spec duration := by
  exact withCellsFrom_property (Transport.id ctx) (genericShapes width)
    (fun cells _ transport _ =>
      genericBody spec (.first (.second (transport.liftInput left)))
        (.second (.second (transport.liftInput left)))
        (.first (.second (transport.liftInput right)))
        (.second (.second (transport.liftInput right))) cells.tail.head.ref cells.head.ref
        (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected ≤ genericDepthLimit spec duration)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      genericBody_depth_le _ _ _ _ _ _ _ _ duration selected) path

/-- Selected generic durations equal the same actual original native trace. -/
theorem genericInto_duration_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (genericInto spec left right output).Path) :
    (genericInto spec left right output).depth duration path =
      (((genericInto spec left right output).eventTrace
        path).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (genericShapes width)
    (fun cells _ transport _ =>
      genericBody spec (.first (.second (transport.liftInput left)))
        (.second (.second (transport.liftInput left)))
        (.first (.second (transport.liftInput right)))
        (.second (.second (transport.liftInput right))) cells.tail.head.ref cells.head.ref
        (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected =>
      genericBody_duration_eventTrace _ _ _ _ _ _ _ _ duration selected) path

private theorem genericBody_resident_le (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericBody spec leftX leftY rightX rightY numerator denominator output).Path) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).peakResidentSpace
      path ≤ genericActiveSpace model.kind width + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (subIntoWord_resident _ _ _ _ path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact (subIntoWord_resident _ _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (affineInto_resident_le _ _ _ _ _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Both persistent slope operands coexist with the largest original active scope. -/
theorem genericInto_resident_le (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericInto spec left right output).Path) :
    (genericInto spec left right output).peakResidentSpace path ≤
      ((genericShapes width).map SpacePool.ofShape).sum + genericActiveSpace model.kind width +
        ctx.residentSpace := by
  exact withCellsFrom_resident_le (Transport.id ctx) (genericShapes width)
    (fun cells _ transport _ =>
      genericBody spec (.first (.second (transport.liftInput left)))
        (.second (.second (transport.liftInput left)))
        (.first (.second (transport.liftInput right)))
        (.second (.second (transport.liftInput right))) cells.tail.head.ref cells.head.ref
        (transport.liftWrite output))
    (genericActiveSpace model.kind width)
    (fun cells _ transport _ selected => genericBody_resident_le _ _ _ _ _ _ _ _ selected) path

private theorem genericBody_auxiliary_le (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericBody spec leftX leftY rightX rightY numerator denominator output).Path) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).peakAuxiliarySpace
      path ≤ genericActiveSpace model.kind width + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (subIntoWord_auxiliary _ _ _ _ path.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact (subIntoWord_auxiliary _ _ _ _ path.2.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (affineInto_auxiliary_le _ _ _ _ _ _ _ path.2.2).trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)

/-- Both persistent slope operands coexist with the largest original active scope. -/
theorem genericInto_auxiliary_le (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width))
    (path : (genericInto spec left right output).Path) :
    (genericInto spec left right output).peakAuxiliarySpace path ≤
      ((genericShapes width).map SpacePool.ofShape).sum + genericActiveSpace model.kind width +
        ctx.auxiliarySpace := by
  exact withCellsFrom_auxiliary_le (Transport.id ctx) (genericShapes width)
    (fun cells _ transport _ =>
      genericBody spec (.first (.second (transport.liftInput left)))
        (.second (.second (transport.liftInput left)))
        (.first (.second (transport.liftInput right)))
        (.second (.second (transport.liftInput right))) cells.tail.head.ref cells.head.ref
        (transport.liftWrite output))
    (genericActiveSpace model.kind width)
    (fun cells _ transport _ selected => genericBody_auxiliary_le _ _ _ _ _ _ _ _ selected) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
