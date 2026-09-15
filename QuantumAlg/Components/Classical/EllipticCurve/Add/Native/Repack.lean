/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual nominal repacking for complete point-addition arms

The original single native point adapter writes the caller destination from
its actual raw tag and two coordinate words. Its full-state interpretation
preserves the complete quantum reference, history and every other stored cell.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original native adapter consumes an actual raw point and writes the nominal destination. -/
def repackOp (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) :
    ClassicalOp (PointEquality.RawPointShape width) (PointShape width) ctx ctx :=
  .packEllipticCurvePoint width ctx raw output

/-- One actual native instruction implements the complete nominal repacking arm. -/
def repackRawInto (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) : Circuit ctx ctx :=
  .classical (repackOp raw output)

/-- The exact caller-store update of the actual native adapter. -/
def repackStore (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) : Store ctx :=
  store.write output (CShape.packEllipticCurvePoint width (store.read raw))

/-- Repacking retains each complete quantum-reference block and records its actual native path. -/
theorem repackRawInto_execute (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (repackRawInto raw output).execute Reference state = state.mapClassical
      (fun entry => (repackStore raw output entry.1, (entry.2, ()))) := rfl

/-- The native output contains exactly the nominal form of the actual incoming raw value. -/
theorem repackRawInto_read_output (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) :
    (repackStore raw output store).read (classifierRead output) =
      CShape.packEllipticCurvePoint width (store.read raw) :=
  Store.read_write_same store output _

/-- Repacking a real complete snapshot restores the exact original nominal point value. -/
theorem repackRawInto_snapshot (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx)
    (value : CShape.Value (PointShape width))
    (snapshot : store.read raw = CShape.unpackEllipticCurvePoint width value) :
    (repackStore raw output store).read (classifierRead output) = value := by
  rw [repackRawInto_read_output, snapshot, CShape.packEllipticCurvePoint_unpackEllipticCurvePoint]

/-- A represented point in the snapshot remains that same semantic point after the actual write. -/
theorem repackRawInto_represents (spec : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx)
    (value : CShape.Value (PointShape width)) (point : Pure.Point spec)
    (snapshot : store.read raw = CShape.unpackEllipticCurvePoint width value)
    (represents : PointRepresents spec value point) :
    PointRepresents spec ((repackStore raw output store).read (classifierRead output)) point := by
  rw [repackRawInto_snapshot raw output store value snapshot]
  exact represents

/-- All structural reads disjoint from the actual destination remain bitwise unchanged. -/
theorem repackRawInto_preserves_read (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : output.key ∉ input.storageKeys) :
    (repackStore raw output store).read input = store.read input :=
  Store.read_write_of_not_mem_storageKeys store output _ input separate

/-- The one original nominal-packing event comes from the same actual native instruction. -/
theorem repackRawInto_eventTrace (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (path : (repackRawInto raw output).Path) :
    (repackRawInto raw output).eventTrace path =
      [.classicalOperation (.nominalEncoding (.packEllipticCurvePoint width))] := rfl

/-- The original single adapter has exactly its independent native duration. -/
theorem repackRawInto_depth (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (duration : Resource.Event kind → Nat)
    (path : (repackRawInto raw output).Path) :
    (repackRawInto raw output).depth duration path =
      duration (.classicalOperation (.nominalEncoding (.packEllipticCurvePoint width))) := rfl

/-- Repacking allocates no storage beyond the actual caller context. -/
theorem repackRawInto_resident (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (path : (repackRawInto raw output).Path) :
    (repackRawInto raw output).peakResidentSpace path = ctx.residentSpace :=
  Circuit.peakResidentSpace_classical _ path

/-- The actual auxiliary roles are unchanged by the native nominal adapter. -/
theorem repackRawInto_auxiliary (raw : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) (path : (repackRawInto raw output).Path) :
    (repackRawInto raw output).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_classical _ path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
