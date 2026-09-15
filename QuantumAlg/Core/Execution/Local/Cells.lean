/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Measurement.Cells

/-!
# Actual local instructions beside existing finite cells

Every finite cell is already resident before this local circuit starts. The
existing single-cell compiler extends the original instructions recursively,
without retaining another cell. The actual outcome path is in bijection with
the original path, including when the cell count is zero. Arbitrary stored
values are permitted; initialization and allocation belong to the caller's
separate actual preparation circuit.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private def localUnderMeasurementCells (code : Circuit ctx ctx) (supported : code.IsLocal)
    (dimension : ℕ+) : (count : Nat) →
    { extended : Circuit (MeasurementCells.context ctx dimension count)
        (MeasurementCells.context ctx dimension count) // extended.IsLocal }
  | 0 => ⟨code, supported⟩
  | count + 1 =>
      let prior := localUnderMeasurementCells code supported dimension count
      let inner := MeasurementCells.context ctx dimension count
      ⟨underRetained prior.val prior.property inner.canonicalFreshKey (.finite dimension)
        inner.canonicalFreshKey_fresh,
        underRetained_isLocal prior.val prior.property inner.canonicalFreshKey (.finite dimension)
          inner.canonicalFreshKey_fresh⟩

/-- Run the original local circuit while keeping all existing finite cells resident. -/
def underMeasurementCells (code : Circuit ctx ctx) (supported : code.IsLocal)
    (dimension : ℕ+) (count : Nat) :
    Circuit (MeasurementCells.context ctx dimension count)
      (MeasurementCells.context ctx dimension count) :=
  (localUnderMeasurementCells code supported dimension count).val

/-- No allocation, release or additional interpreter is introduced by the extension. -/
theorem underMeasurementCells_isLocal (code : Circuit ctx ctx) (supported : code.IsLocal)
    (dimension : ℕ+) (count : Nat) :
    (underMeasurementCells code supported dimension count).IsLocal :=
  (localUnderMeasurementCells code supported dimension count).property

/-- The existing measurement cells add no outcome or branch choice to the actual path. -/
def underMeasurementCellsPathEquiv (code : Circuit ctx ctx) (supported : code.IsLocal)
    (dimension : ℕ+) : (count : Nat) →
    code.Path ≃ (underMeasurementCells code supported dimension count).Path
  | 0 => Equiv.refl _
  | count + 1 =>
      let prior := localUnderMeasurementCells code supported dimension count
      let inner := MeasurementCells.context ctx dimension count
      (underMeasurementCellsPathEquiv code supported dimension count).trans
        (underRetainedPathEquiv prior.val prior.property inner.canonicalFreshKey
          (.finite dimension) inner.canonicalFreshKey_fresh)

end

end QuantumAlg.Circuit
