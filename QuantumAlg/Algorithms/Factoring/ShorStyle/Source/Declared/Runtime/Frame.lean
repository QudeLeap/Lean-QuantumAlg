/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Outcome
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Structural reads outside a declared Shor observation

The actual phase-cell writes and paid result packing preserve any old
structural read separated from their physical destinations. This permits a
conditional Born law to carry earlier sample data and its reference matrix.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)
  (sameWires : base.quantumWires = (layout N).wires)

private theorem frame_readout_key (index : Fin (phaseBits N)) :
    (readout base N sameWires index).output.key =
      (Storage.cells base N index).key :=
  FiniteReadout.transported_key
    (shorDeclared_context_qubits N
      ((Storage.quantumWires base N).trans sameWires) _)
    (Storage.cells base N index)

/-- The selected physical phase measurement and paid packing retain an
old structural read outside their measurement cells and working result. -/
theorem measured_packed_frame {shape : CShape}
    (observed : CInputRef (Storage.context base N) shape)
    (measuredSeparate : ∀ index : Fin (phaseBits N),
      (Storage.cells base N index).key ∉ observed.storageKeys)
    (workingSeparate :
      (Storage.resultRef base N).key ∉ observed.storageKeys)
    (store : Store (Storage.context base N))
    (basis : (Storage.context base N).register.Index) :
    ((measuredStore base N input sameWires store basis).applyOp
      (packing base N)).read observed = store.read observed := by
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (packing base N) observed workingSeparate).trans ?_
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rw [frame_readout_key base N sameWires index]
  exact measuredSeparate index

/-- Newly allocated measurement destinations cannot overwrite an original structural input. -/
theorem measured_packed_liftInput {shape : CShape} (observed : CInputRef base shape)
    (store : Store (Storage.context base N))
    (basis : (Storage.context base N).register.Index) :
    ((measuredStore base N input sameWires store basis).applyOp
      (packing base N)).read (Storage.liftInput base N observed) =
        store.read (Storage.liftInput base N observed) := by
  apply measured_packed_frame base N input sameWires
  · intro index
    exact MeasurementCells.reference_not_mem_liftInput 2
      (observed.underRetained base.canonicalFreshKey (.bits (phaseBits N))
        base.canonicalFreshKey_fresh) (phaseBits N) index
  · change (MeasurementCells.liftWrite 2
      (CWriteRef.retainedHead base base.canonicalFreshKey (.bits (phaseBits N))
        base.canonicalFreshKey_fresh) (phaseBits N)).key ∉
        (MeasurementCells.liftInput 2
          (observed.underRetained base.canonicalFreshKey (.bits (phaseBits N))
            base.canonicalFreshKey_fresh) (phaseBits N)).storageKeys
    rw [MeasurementCells.liftWrite_key, MeasurementCells.liftInput_storageKeys]
    exact CInputRef.fresh_not_mem_storageKeys_underRetained observed
      base.canonicalFreshKey (.bits (phaseBits N)) base.canonicalFreshKey_fresh

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
