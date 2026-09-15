/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Infinity
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Actual original resources of infinity initialization

The same two native instructions and three internal cells supply the event,
dependency-depth and live-space bounds. No caller zero word is supplied free.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original tag-not and nominal-point packing event sequence. -/
def infinityTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.bit .not),
    .classicalOperation (.nominalEncoding (.packEllipticCurvePoint width))]

private theorem infinityBody_eventTrace (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody falseBit tag zero output).Path) :
    (infinityBody falseBit tag zero output).eventTrace path = infinityTrace width := rfl

/-- Actual internal allocation and release add no event beyond the original two instructions. -/
theorem infinityInto_eventTrace (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto output).Path) :
    (infinityInto output).eventTrace path = infinityTrace width := by
  exact withCellsFrom_property (Transport.id ctx) (infinityShapes width)
    (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = infinityTrace width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => infinityBody_eventTrace _ _ _ _ selected) path

/-- The same executed trace gives the exact original native event multiplicities. -/
theorem infinityInto_resourcePool (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto output).Path) :
    (infinityInto output).resourcePool path = ResourcePool.ofList (infinityTrace width) :=
  congrArg ResourcePool.ofList (infinityInto_eventTrace output path)

private theorem infinityBody_depth (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (duration : Resource.Event kind → Nat)
    (path : (infinityBody falseBit tag zero output).Path) :
    (infinityBody falseBit tag zero output).depth duration path =
      ((infinityTrace width).map duration).sum := by
  change duration _ + duration _ = duration _ + (duration _ + 0)
  simp only [add_zero]
  rfl

/-- The actual dependency depth retains both original instruction durations. -/
theorem infinityInto_depth (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event kind → Nat) (path : (infinityInto output).Path) :
    (infinityInto output).depth duration path = ((infinityTrace width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (infinityShapes width)
    (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((infinityTrace width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => infinityBody_depth _ _ _ _ duration selected) path

/-- Unit native durations give the original two-step infinity initialization. -/
theorem infinityInto_unitDepth (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto output).Path) :
    (infinityInto output).depth (fun _ => 1) path = 2 := by
  rw [infinityInto_depth]
  rfl

private theorem infinityBody_resident (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody falseBit tag zero output).Path) :
    (infinityBody falseBit tag zero output).peakResidentSpace path ≤ ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

private theorem infinityBody_auxiliary (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody falseBit tag zero output).Path) :
    (infinityBody falseBit tag zero output).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

/-- The original false, tag and zero cells bound the full actual resident peak. -/
theorem infinityInto_resident (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto output).Path) :
    (infinityInto output).peakResidentSpace path ≤
      ((infinityShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, infinityInto, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (infinityShapes width)
      (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
        (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using infinityBody_resident _ _ _ _ selected) path

/-- The same three internally allocated cells carry their actual auxiliary roles. -/
theorem infinityInto_auxiliary (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto output).Path) :
    (infinityInto output).peakAuxiliarySpace path ≤
      ((infinityShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, infinityInto, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (infinityShapes width)
      (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
        (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using infinityBody_auxiliary _ _ _ _ selected) path

/-- A full zero-coordinate word and two real bits have the original scratch capacity. -/
theorem infinityShapes_classicalBits :
    (((infinityShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits =
      width + 2 := by
  simp [infinityShapes, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
