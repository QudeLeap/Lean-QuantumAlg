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

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- The original tag-not and nominal-point packing event sequence. -/
def infinityTrace (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packEllipticCurvePoint width)))]

private lemma infinityBody_eventTrace (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody (model := model) falseBit tag zero output).Path) :
    (infinityBody (model := model) falseBit tag zero output).eventTrace path =
      infinityTrace model width := by
  unfold infinityBody at path ⊢
  change (BitWord.instruction (execution := model) (infinityTagOp falseBit tag)).eventTrace
      path.1 ++
    (repackRawInto (model := model) (infinityRaw tag zero) output).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace, repackRawInto_eventTrace]
  rfl

/-- Actual internal allocation and release add no event beyond the original two instructions. -/
lemma infinityInto_eventTrace (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).eventTrace path = infinityTrace model width := by
  exact withCellsFrom_property (Transport.id ctx) (infinityShapes width)
    (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.eventTrace selected = infinityTrace model width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => infinityBody_eventTrace _ _ _ _ selected) path

/-- The same executed trace gives the exact original native event multiplicities. -/
lemma infinityInto_resourcePool (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).resourcePool path =
      ResourcePool.ofList (infinityTrace model width) :=
  congrArg ResourcePool.ofList (infinityInto_eventTrace output path)

private lemma infinityBody_depth (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (duration : Resource.Event model → Nat)
    (path : (infinityBody (model := model) falseBit tag zero output).Path) :
    (infinityBody (model := model) falseBit tag zero output).depth duration path =
      ((infinityTrace model width).map duration).sum := by
  unfold infinityBody at path ⊢
  change (BitWord.instruction (execution := model) (infinityTagOp falseBit tag)).depth
      duration path.1 +
    (repackRawInto (model := model) (infinityRaw tag zero) output).depth duration path.2 = _
  rw [BitWord.bitWord_instruction_depth, repackRawInto_depth]
  rfl

/-- The actual dependency depth retains both original instruction durations. -/
lemma infinityInto_depth (output : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).depth duration path =
      ((infinityTrace model width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (infinityShapes width)
    (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
      (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((infinityTrace model width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => infinityBody_depth _ _ _ _ duration selected) path

/-- Unit native durations give the original two-step infinity initialization. -/
lemma infinityInto_unitDepth (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).depth (fun _ => 1) path = 2 := by
  rw [infinityInto_depth]
  rfl

private lemma infinityBody_resident (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody (model := model) falseBit tag zero output).Path) :
    (infinityBody (model := model) falseBit tag zero output).peakResidentSpace path ≤
      ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

private lemma infinityBody_auxiliary (falseBit : CInputRef ctx .bit)
    (tag : CWriteRef ctx .bit) (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width))
    (path : (infinityBody (model := model) falseBit tag zero output).Path) :
    (infinityBody (model := model) falseBit tag zero output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

/-- The original false, tag and zero cells bound the full actual resident peak. -/
lemma infinityInto_resident (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).peakResidentSpace path ≤
      ((infinityShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, infinityInto, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (infinityShapes width)
      (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
        (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using infinityBody_resident _ _ _ _ selected) path

/-- The same three internally allocated cells carry their actual auxiliary roles. -/
lemma infinityInto_auxiliary (output : CWriteRef ctx (PointShape width))
    (path : (infinityInto (model := model) output).Path) :
    (infinityInto (model := model) output).peakAuxiliarySpace path ≤
      ((infinityShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, infinityInto, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (infinityShapes width)
      (fun cells _ transport _ => infinityBody (classifierRead cells.head.ref) cells.tail.head.ref
        (classifierRead cells.tail.tail.head.ref) (transport.liftWrite output)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using infinityBody_auxiliary _ _ _ _ selected) path

omit [BitWord.Selected model] in
/-- A full zero-coordinate word and two real bits have the original scratch capacity. -/
lemma infinityShapes_classicalBits :
    (((infinityShapes width).map (SpacePool.ofShape (kind := model.kind))).sum) .classicalBits =
      width + 2 := by
  simp [infinityShapes, SpacePool.ofShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
