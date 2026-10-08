/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Cells
import all QuantumAlg.Core.Execution.Local.Retained.Resources

/-!
# Native resources of actual local execution beside finite cells

The same original instructions have the same ordered native events and
evaluated depth. Every existing finite cell remains charged in both space
accounts throughout execution. The count may be zero, and durations may be
assigned independently to each native event.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution ContextUnion

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
  (code : Circuit model ctx ctx) (supported : code.IsLocal) (dimension : ℕ+) (count : Nat)

/-- The actual path executes exactly the original ordered native events. -/
theorem underMeasurementCells_eventTrace (path : code.Path) :
    (underMeasurementCells code supported dimension count).eventTrace
      (underMeasurementCellsPathEquiv code supported dimension count path) =
        code.eventTrace path := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (underRetained_eventTrace _ _ _ _ _ _).trans ih

/-- Every native event multiplicity is unchanged on the corresponding actual path. -/
theorem underMeasurementCells_resourcePool (path : code.Path) :
    (underMeasurementCells code supported dimension count).resourcePool
      (underMeasurementCellsPathEquiv code supported dimension count path) =
        code.resourcePool path :=
  congrArg ResourcePool.ofList
    (underMeasurementCells_eventTrace code supported dimension count path)

/-- Every assignment of native durations has exactly the original evaluated depth. -/
theorem underMeasurementCells_depth (duration : Resource.Event model → Nat) (path : code.Path) :
    (underMeasurementCells code supported dimension count).depth duration
      (underMeasurementCellsPathEquiv code supported dimension count path) =
        code.depth duration path := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (underRetained_depth _ _ _ _ _ duration _).trans ih

/-- Every visited context includes the same actual finite cells and original resources. -/
theorem underMeasurementCells_visited
    (path : (underMeasurementCells code supported dimension count).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈
      (underMeasurementCells code supported dimension count).visitedContexts path) :
    visited = MeasurementCells.context ctx dimension count :=
  local_visited _ (underMeasurementCells_isLocal code supported dimension count)
    path visited present

/-- The exact resident peak counts the native encoding of every retained finite cell. -/
theorem underMeasurementCells_peakResidentSpace
    (path : (underMeasurementCells code supported dimension count).Path) :
    (underMeasurementCells code supported dimension count).peakResidentSpace path =
      count • SpacePool.ofShape (.finite dimension) + ctx.residentSpace := by
  let compiled := underMeasurementCells code supported dimension count
  have upper := compiled.peakResidentSpace_le_of_visited path
    (MeasurementCells.context ctx dimension count).residentSpace (by
      intro visited present
      exact (congrArg RuntimeCtx.residentSpace
        (underMeasurementCells_visited code supported dimension count path visited present)).le)
  have lower := compiled.residentSpace_le_peak_of_visited path
    (MeasurementCells.context ctx dimension count)
    (local_pre_mem compiled (underMeasurementCells_isLocal code supported dimension count) path)
  exact (le_antisymm upper lower).trans (MeasurementCells.context_residentSpace ctx dimension count)

/-- The same actual retained roles contribute their full encodings to the auxiliary peak. -/
theorem underMeasurementCells_peakAuxiliarySpace
    (path : (underMeasurementCells code supported dimension count).Path) :
    (underMeasurementCells code supported dimension count).peakAuxiliarySpace path =
      count • SpacePool.ofShape (.finite dimension) + ctx.auxiliarySpace := by
  let compiled := underMeasurementCells code supported dimension count
  have upper := compiled.peakAuxiliarySpace_le_of_visited path
    (MeasurementCells.context ctx dimension count).auxiliarySpace (by
      intro visited present
      exact (congrArg RuntimeCtx.auxiliarySpace
        (underMeasurementCells_visited code supported dimension count path visited present)).le)
  have lower := compiled.auxiliarySpace_le_peak_of_visited path
    (MeasurementCells.context ctx dimension count)
    (local_pre_mem compiled (underMeasurementCells_isLocal code supported dimension count) path)
  exact (le_antisymm upper lower).trans
    (MeasurementCells.context_auxiliarySpace ctx dimension count)

end

end QuantumAlg.Circuit
