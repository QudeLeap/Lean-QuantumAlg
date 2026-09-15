/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.PointEquality.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Original resources of the actual native point comparator

The actual eight instructions emit the original event list in its original
order. Both point snapshots and all three intermediate bits remain live in
real lexical storage until the comparison ends, then those same cells leave.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual native core emits exactly the original eight classical events. -/
theorem core_eventTrace (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit)
    (path : (core left right scratch output).Path) :
    (core left right scratch output).eventTrace path = coreTrace width := by
  simp [core, Circuit.forRange, stage, Circuit.eventTrace, ClassicalOp.eventTrace,
    unpackLeft, unpackRight, tagXor, tagNot, equalX, equalY, coordinateAnd, outputAnd,
    coreTrace, ClassicalOp.event, ClassicalOp.label]

/-- Internal lexical allocation and release preserve that exact chronological event list. -/
theorem compareInto_eventTrace (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    (compareInto left right output).eventTrace path = coreTrace width := by
  exact withCellsFrom_property (Transport.id ctx) (scratchShapes width)
    (fun cells _ transport _ => core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = coreTrace width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => core_eventTrace _ _ _ _ selected) path

/-- The exact original event multiplicities belong to the actual allocated circuit. -/
theorem compareInto_resourcePool (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    (compareInto left right output).resourcePool path = coreEnvelope width := by
  exact congrArg ResourcePool.ofList (compareInto_eventTrace left right output path)

/-- Every actual path contains exactly eight classical instructions. -/
theorem compareInto_eventCount (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    ((compareInto left right output).eventTrace path).length = 8 := by
  rw [compareInto_eventTrace]
  rfl

private theorem core_depth (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit)
    (duration : Resource.Event kind → Nat) (path : (core left right scratch output).Path) :
    (core left right scratch output).depth duration path =
      ((coreTrace width).map duration).sum := by
  simp [core, Circuit.forRange, stage, Circuit.depth, Circuit.eventDepth, DepthExpr.depthEval,
    unpackLeft, unpackRight, tagXor, tagNot, equalX, equalY, coordinateAnd, outputAnd,
    coreTrace, ClassicalOp.event, ClassicalOp.label]

/-- The actual serial dependency depth includes each original native event duration. -/
theorem compareInto_depth (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (duration : Resource.Event kind → Nat)
    (path : (compareInto left right output).Path) :
    (compareInto left right output).depth duration path =
      ((coreTrace width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (scratchShapes width)
    (fun cells _ transport _ => core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((coreTrace width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => core_depth _ _ _ _ duration selected) path

/-- Unit native durations give the original eight sequential comparison steps. -/
theorem compareInto_unitDepth (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    (compareInto left right output).depth (fun _ => 1) path = 8 := by
  rw [compareInto_depth]
  rfl

private theorem core_resident (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit)
    (path : (core left right scratch output).Path) :
    (core left right scratch output).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.forRange_resident_le 8 _ _ le_rfl _ path
  intro index selected
  fin_cases index <;> exact (Circuit.peakResidentSpace_classical _ selected).le

private theorem core_auxiliary (left right : CInputRef ctx (PointShape width))
    (scratch : Scratch ctx width) (output : CWriteRef ctx .bit)
    (path : (core left right scratch output).Path) :
    (core left right scratch output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.forRange_auxiliary_le 8 _ _ le_rfl _ path
  intro index selected
  fin_cases index <;> exact (Circuit.peakAuxiliarySpace_classical _ selected).le

/-- The original five complete scratch shapes bound the actual resident peak. -/
theorem compareInto_resident (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    (compareInto left right output).peakResidentSpace path ≤
      ((scratchShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, compareInto, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (scratchShapes width)
    (fun cells _ transport _ => core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output)) 0
    (by
      intro inner cells distinct transport separated selected
      simpa only [zero_add] using core_resident
        (transport.liftInput left) (transport.liftInput right)
        (scratchOfCells cells) (transport.liftWrite output) selected) path

/-- Every internally allocated point and intermediate bit is charged as actual auxiliary space. -/
theorem compareInto_auxiliary (left right : CInputRef ctx (PointShape width))
    (output : CWriteRef ctx .bit) (path : (compareInto left right output).Path) :
    (compareInto left right output).peakAuxiliarySpace path ≤
      ((scratchShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, compareInto, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (scratchShapes width)
    (fun cells _ transport _ => core (transport.liftInput left) (transport.liftInput right)
      (scratchOfCells cells) (transport.liftWrite output)) 0
    (by
      intro inner cells distinct transport separated selected
      simpa only [zero_add] using core_auxiliary
        (transport.liftInput left) (transport.liftInput right)
        (scratchOfCells cells) (transport.liftWrite output) selected) path

/-- Two complete raw points and three bits occupy exactly the original scratch bit allowance. -/
theorem scratchShapes_classicalBits :
    (((scratchShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits =
      4 * width + 5 := by
  simp [scratchShapes, RawPointShape, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.PointEquality.Native
