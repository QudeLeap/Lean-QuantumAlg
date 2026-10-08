/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.ScalarMul.Native
import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Complete.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Original native event and duration bounds for scalar multiplication

Each declared slot includes its real doubling and the stored-bit choice of
addition or identity. Their original complete-addition allowances compose
with the two actual infinity instructions. Fresh result allocation adds no
native operation. Exact duration equations use the same actual event trace.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- Two original initialization events and both original additions in every declared slot. -/
def scalarEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (spec : CurveSpec width) (scalarWidth : Nat) : ResourcePool model :=
  ResourcePool.ofList (Add.Native.infinityTrace model width) +
    ResourcePool.scale scalarWidth
      (Add.Native.additionEnvelope model spec + Add.Native.additionEnvelope model spec)

/-- Original serial durations preserve all scalar slots, including leading zero bits. -/
def scalarDepthLimit {model : ExecutionModel} [BitWord.Selected model]
    (spec : CurveSpec width) (scalarWidth : Nat)
    (duration : Resource.Event model → Nat) : Nat :=
  ((Add.Native.infinityTrace model width).map duration).sum +
    scalarWidth * (Add.Native.additionDepthLimit spec duration +
      Add.Native.additionDepthLimit spec duration)

private theorem scalarBitArm_pool_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (path : (scalarBitArm spec point accumulator value).Path) :
    (scalarBitArm spec point accumulator value).resourcePool path ≤
      Add.Native.additionEnvelope model spec := by
  cases value with
  | bit flag =>
      cases flag
      · exact Multiset.zero_le _
      · exact Add.Native.addInto_pool_le spec _ point accumulator path

private theorem scalarSlot_pool_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (path : (scalarSlot spec bits point accumulator index).Path) :
    (scalarSlot spec bits point accumulator index).resourcePool path ≤
      Add.Native.additionEnvelope model spec + Add.Native.additionEnvelope model spec := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Add.Native.addInto_pool_le spec _ _ accumulator path.1)
    (scalarBitArm_pool_le spec point accumulator path.2.1 path.2.2)

/-- Every real path meets the original two-call allowance of every declared scalar slot. -/
theorem scalarInto_pool_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (path : (scalarInto spec bits point accumulator).Path) :
    (scalarInto spec bits point accumulator).resourcePool path ≤
      scalarEnvelope model spec scalarWidth := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Add.Native.infinityInto_resourcePool accumulator path.1).le
    (Circuit.forRange_pool_le scalarWidth (scalarSlot spec bits point accumulator) _
      (scalarSlot_pool_le spec bits point accumulator) path.2)

/-- Actual retained allocation preserves the original scalar event allowance. -/
theorem scalarRetained_pool_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (scalarRetained spec bits point key fresh).Path) :
    (scalarRetained spec bits point key fresh).resourcePool path ≤
      scalarEnvelope model spec scalarWidth :=
  scalarInto_pool_le spec _ _ _ path.2

private theorem scalarBitArm_depth_le (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (duration : Resource.Event model → Nat)
    (path : (scalarBitArm spec point accumulator value).Path) :
    (scalarBitArm spec point accumulator value).depth duration path ≤
      Add.Native.additionDepthLimit spec duration := by
  cases value with
  | bit flag =>
      cases flag
      · exact Nat.zero_le _
      · exact Add.Native.addInto_depth_le spec _ point accumulator duration path

private theorem scalarSlot_depth_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (duration : Resource.Event model → Nat)
    (path : (scalarSlot spec bits point accumulator index).Path) :
    (scalarSlot spec bits point accumulator index).depth duration path ≤
      Add.Native.additionDepthLimit spec duration + Add.Native.additionDepthLimit spec duration :=
  Nat.add_le_add (Add.Native.addInto_depth_le spec _ _ accumulator duration path.1)
    (scalarBitArm_depth_le spec point accumulator path.2.1 duration path.2.2)

/-- Native durations compose along the same real scalar program, without parallel shortcuts. -/
theorem scalarInto_depth_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat) (path : (scalarInto spec bits point accumulator).Path) :
    (scalarInto spec bits point accumulator).depth duration path ≤
      scalarDepthLimit spec scalarWidth duration := by
  have folded := Circuit.forRange_depth_le_sum scalarWidth
    (scalarSlot spec bits point accumulator) duration
    (fun _ => Add.Native.additionDepthLimit spec duration +
      Add.Native.additionDepthLimit spec duration)
    (fun index => scalarSlot_depth_le spec bits point accumulator index duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at folded
  exact Nat.add_le_add (Add.Native.infinityInto_depth accumulator duration path.1).le folded

/-- Real retained allocation adds no dependency event to the complete scalar program. -/
theorem scalarRetained_depth_le (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (duration : Resource.Event model → Nat)
    (path : (scalarRetained spec bits point key fresh).Path) :
    (scalarRetained spec bits point key fresh).depth duration path ≤
      scalarDepthLimit spec scalarWidth duration := by
  change 0 + _ ≤ _
  rw [zero_add]
  exact scalarInto_depth_le spec _ _ _ duration path.2

private theorem scalarBitArm_duration_eventTrace (spec : CurveSpec width)
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (value : CShape.Value .bit) (duration : Resource.Event model → Nat)
    (path : (scalarBitArm spec point accumulator value).Path) :
    (scalarBitArm spec point accumulator value).depth duration path =
      (((scalarBitArm spec point accumulator value).eventTrace path).map duration).sum := by
  cases value with
  | bit flag =>
      cases flag
      · rfl
      · exact Add.Native.addInto_duration_eventTrace spec _ point accumulator duration path

private theorem scalarSlot_duration_eventTrace (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (index : Fin scalarWidth) (duration : Resource.Event model → Nat)
    (path : (scalarSlot spec bits point accumulator index).Path) :
    (scalarSlot spec bits point accumulator index).depth duration path =
      (((scalarSlot spec bits point accumulator index).eventTrace path).map duration).sum := by
  change _ + _ = (List.map duration (_ ++ _)).sum
  rw [List.map_append, List.sum_append]
  exact congrArg₂ (· + ·)
    (Add.Native.addInto_duration_eventTrace spec _ _ accumulator duration path.1)
    (scalarBitArm_duration_eventTrace spec point accumulator path.2.1 duration path.2.2)

/-- Complete dependency depth equals the durations of precisely the same executed native events. -/
theorem scalarInto_duration_eventTrace (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (accumulator : CWriteRef ctx (PointShape width))
    (duration : Resource.Event model → Nat) (path : (scalarInto spec bits point accumulator).Path) :
    (scalarInto spec bits point accumulator).depth duration path =
      (((scalarInto spec bits point accumulator).eventTrace path).map duration).sum := by
  change _ + _ = (List.map duration (_ ++ _)).sum
  rw [List.map_append, List.sum_append]
  refine congrArg₂ (· + ·) ?_
    (Circuit.forRange_duration_eventTrace scalarWidth (scalarSlot spec bits point accumulator)
      duration (fun index => scalarSlot_duration_eventTrace spec bits point accumulator index
        duration) path.2)
  rw [Add.Native.infinityInto_eventTrace]
  exact Add.Native.infinityInto_depth accumulator duration path.1

/-- Allocation retains its real result while leaving the exact scalar event-duration equation. -/
theorem scalarRetained_duration_eventTrace (spec : CurveSpec width)
    (bits : CInputRef ctx (.fixedVector scalarWidth .bit))
    (point : CInputRef ctx (PointShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (duration : Resource.Event model → Nat)
    (path : (scalarRetained spec bits point key fresh).Path) :
    (scalarRetained spec bits point key fresh).depth duration path =
      (((scalarRetained spec bits point key fresh).eventTrace path).map duration).sum := by
  change 0 + _ = (([] ++ _).map duration).sum
  simp only [zero_add, List.nil_append]
  exact scalarInto_duration_eventTrace spec _ _ _ duration path.2

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.ScalarMul.Native
