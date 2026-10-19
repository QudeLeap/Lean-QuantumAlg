/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Retained
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

/-!
# Native execution beside already resident finite cells

The child is an actual allocation-free circuit. Each existing retained head
uses two native placements, first into the disjoint union and then along the
same entry permutation. No child syntax is inspected or rebuilt, no cell is
allocated, and every actual event and path is preserved.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Place the original child beside one existing retained head, in its exact old coordinates. -/
def embedRetained (code : Circuit model ctx ctx false)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    Circuit model (ctx.addRetained key shape fresh) (ctx.addRetained key shape fresh) false :=
  .embed (ContextEmbedding.alongPermutation (retainedLocalPermutation ctx key shape fresh))
    (.embed (ContextEmbedding.alongUnion ctx (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)) code)

/-- Keep every already resident measurement cell around the original allocation-free child. -/
def embedMeasurementCells (code : Circuit model ctx ctx false) (dimension : ℕ+) :
    (count : Nat) → Circuit model (MeasurementCells.context ctx dimension count)
      (MeasurementCells.context ctx dimension count) false
  | 0 => code
  | count + 1 =>
      let inner := MeasurementCells.context ctx dimension count
      embedRetained (embedMeasurementCells code dimension count) inner.canonicalFreshKey
        (.finite dimension) inner.canonicalFreshKey_fresh

/-- Existing finite storage introduces no additional actual outcome or branch choice. -/
def embedMeasurementCellsPathEquiv (code : Circuit model ctx ctx false) (dimension : ℕ+) :
    (count : Nat) → code.Path ≃ (embedMeasurementCells code dimension count).Path
  | 0 => Equiv.refl _
  | count + 1 => embedMeasurementCellsPathEquiv code dimension count

/-- Every native child event remains in its original order. -/
lemma embedMeasurementCells_eventTrace (code : Circuit model ctx ctx false)
    (dimension : ℕ+) (count : Nat) (path : code.Path) :
    (embedMeasurementCells code dimension count).eventTrace
      (embedMeasurementCellsPathEquiv code dimension count path) = code.eventTrace path := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

/-- Every original event multiplicity belongs to the same actual child path. -/
lemma embedMeasurementCells_resourcePool (code : Circuit model ctx ctx false)
    (dimension : ℕ+) (count : Nat) (path : code.Path) :
    (embedMeasurementCells code dimension count).resourcePool
      (embedMeasurementCellsPathEquiv code dimension count path) = code.resourcePool path :=
  congrArg ResourcePool.ofList (embedMeasurementCells_eventTrace code dimension count path)

/-- Arbitrary native event durations are unchanged on the original child path. -/
lemma embedMeasurementCells_depth (code : Circuit model ctx ctx false)
    (dimension : ℕ+) (count : Nat) (duration : Resource.Event model → Nat) (path : code.Path) :
    (embedMeasurementCells code dimension count).depth duration
      (embedMeasurementCellsPathEquiv code dimension count path) = code.depth duration path := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

end

end QuantumAlg.Circuit
