/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Actual resources of the original public XGCD packing

The real five operations and their serial dependencies are charged exactly.
The two coefficient resizes reuse one word, while both signed coefficients
stay resident until the final product pack. All caller storage remains live.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual allocation and release add no events to the original five packing instructions. -/
theorem xgcdNativePackRawOutputs_eventTrace (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).eventTrace path = packingEvents kind width := by
  exact withCellsFrom_property (Transport.id ctx) (packingShapes width)
    (fun cells _ transport _ => packingBody (outputs.transport transport) cells.head.ref
      cells.tail.head.ref cells.tail.tail.head.ref (transport.liftWrite result))
    (fun _ code => ∀ selected, code.eventTrace selected = packingEvents kind width)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => xgcdNativePackingBody_eventTrace _ _ _ _ _ selected) path

/-- The original native resource pool is computed from the same actual event trace. -/
theorem xgcdNativePackRawOutputs_resourcePool (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).resourcePool path =
      ResourcePool.ofList (packingEvents kind width) :=
  congrArg ResourcePool.ofList (xgcdNativePackRawOutputs_eventTrace outputs result path)

private theorem packingBody_depth (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (packingBody outputs raw left right result).Path) :
    (packingBody outputs raw left right result).depth duration path =
      ((packingEvents kind width).map duration).sum := by
  change _ + (_ + (_ + (_ + _))) = _ + (_ + (_ + (_ + (_ + 0))))
  simp only [add_zero]
  rfl

/-- Arbitrary native durations preserve every original serial dependency. -/
theorem xgcdNativePackRawOutputs_depth (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width)) (duration : Resource.Event kind → Nat)
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).depth duration path =
      ((packingEvents kind width).map duration).sum := by
  exact withCellsFrom_property (Transport.id ctx) (packingShapes width)
    (fun cells _ transport _ => packingBody (outputs.transport transport) cells.head.ref
      cells.tail.head.ref cells.tail.tail.head.ref (transport.liftWrite result))
    (fun _ code => ∀ selected, code.depth duration selected =
      ((packingEvents kind width).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun cells _ transport _ selected => packingBody_depth _ _ _ _ _ duration selected) path

/-- Exactly five original native operations remain on the actual serial path. -/
theorem xgcdNativePackRawOutputs_unitDepth (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).depth (fun _ => 1) path = 5 := by
  rw [xgcdNativePackRawOutputs_depth]
  rfl

private theorem packingBody_resident (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packingBody outputs raw left right result).Path) :
    (packingBody outputs raw left right result).peakResidentSpace path ≤ ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace
      (SpacePool.max ctx.residentSpace 0)))) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

private theorem packingBody_auxiliary (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packingBody outputs raw left right result).Path) :
    (packingBody outputs raw left right result).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace
      (SpacePool.max ctx.auxiliarySpace 0)))) ≤ _
  simp only [SpacePool.max_zero, SpacePool.max_self, le_refl]

/-- The complete resident peak includes the original three packing cells and every caller cell. -/
theorem xgcdNativePackRawOutputs_resident (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).peakResidentSpace path ≤
      ((packingShapes width).map SpacePool.ofShape).sum + ctx.residentSpace := by
  simpa only [add_zero, packRawOutputs, withCells] using
    withCellsFrom_resident_le (Transport.id ctx) (packingShapes width)
      (fun cells _ transport _ => packingBody (outputs.transport transport) cells.head.ref
        cells.tail.head.ref cells.tail.tail.head.ref (transport.liftWrite result)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using packingBody_resident _ _ _ _ _ selected) path

/-- Every internally allocated packing cell contributes to the actual auxiliary peak. -/
theorem xgcdNativePackRawOutputs_auxiliary (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packRawOutputs outputs result).Path) :
    (packRawOutputs outputs result).peakAuxiliarySpace path ≤
      ((packingShapes width).map SpacePool.ofShape).sum + ctx.auxiliarySpace := by
  simpa only [add_zero, packRawOutputs, withCells] using
    withCellsFrom_auxiliary_le (Transport.id ctx) (packingShapes width)
      (fun cells _ transport _ => packingBody (outputs.transport transport) cells.head.ref
        cells.tail.head.ref cells.tail.tail.head.ref (transport.liftWrite result)) 0
      (by
        intro inner cells _ transport _ selected
        simpa only [zero_add] using packingBody_auxiliary _ _ _ _ _ selected) path

/-- One narrowing word and two signed words occupy their full public coefficient widths. -/
theorem xgcdNativePackingShapes_classicalBits :
    (((packingShapes width).map (SpacePool.ofShape (kind := kind))).sum) .classicalBits =
      3 * coefficientWidth width := by
  simp [packingShapes, SpacePool.ofShape, SignedShape, CShape.bitWidth]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
