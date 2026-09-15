/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Store.Read

/-!
# The actual first-batch measurement cells are separate from sampled data

The finite-cell allocator uses fresh keys after the actual sampler and owned
bank preparation. Every measured cell is distinct, and every structural
sampler operand remains below those cells. Consequently no round overwrites
its sampled parameter or original source bits. These are properties of the
constructed storage layout, with no added input-state assumption.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

private theorem measurement_input_separate {ctx : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef ctx shape) (dimension : ℕ+) (count : Nat) :
    ∀ index : Fin count, (MeasurementCells.reference ctx dimension count index).key ∉
      (MeasurementCells.liftInput dimension input count).storageKeys := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count induction =>
      intro index
      refine Fin.cases ?_ (fun index => ?_) index
      · exact CInputRef.fresh_not_mem_storageKeys_underRetained
          (MeasurementCells.liftInput dimension input count)
          (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
          (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh
      · change (MeasurementCells.reference ctx dimension count index).key ∉
          ((MeasurementCells.liftInput dimension input count).underRetained
            (MeasurementCells.context ctx dimension count).canonicalFreshKey (.finite dimension)
            (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh).storageKeys
        rw [CInputRef.storageKeys_underRetained]
        exact induction index

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every measured source bit writes to its own distinct actual finite cell. -/
theorem nativeBatch_cells_distinct :
    Function.Injective (fun index => (cells base noQuantum N index).key) :=
  MeasurementCells.reference_key_injective (bankContext base noQuantum N) 2 (measurementBits N)

/-- No actual measured cell aliases any structural operand of the completed sampler. -/
theorem nativeBatch_cells_input_separate {shape : CShape}
    (input : CInputRef (sampledContext base N) shape) (index : Fin (measurementBits N)) :
    (cells base noQuantum N index).key ∉ (readyInput base noQuantum N input).storageKeys :=
  measurement_input_separate (bankInput base noQuantum N input) 2 (measurementBits N) index

/-- The actual sampled parameter and any earlier sampled data survive each round's finite writes. -/
theorem nativeBatch_cells_parameter_separate {shape : CShape}
    (previous : CInputRef (sampledContext base N) shape) (index : Fin (measurementBits N)) :
    (cells base noQuantum N index).key ∉
      (CInputRef.product (parameter base noQuantum N)
        (readyInput base noQuantum N previous)).storageKeys := by
  intro present
  rcases List.mem_append.mp present with parameterKey | previousKey
  · exact nativeBatch_cells_input_separate base noQuantum N
      (.storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef)
      index parameterKey
  · exact nativeBatch_cells_input_separate base noQuantum N previous index previousKey

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
