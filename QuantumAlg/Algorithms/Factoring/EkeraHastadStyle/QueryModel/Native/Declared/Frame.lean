/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Outcome
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Structural reads outside a declared EH observation

The actual exponent-cell writes and paid result packing preserve any old
structural read separated from their physical destinations. This permits a
conditional Born law to carry earlier sample data and its reference matrix.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat)

private lemma readout_key (index : Fin (measurementBits N)) :
    (readout base noQuantum N index).output.key =
      (Native.cells base noQuantum N index).key :=
  FiniteReadout.transported_key
    (Native.nativeOracle_context_qubits N
      (Native.nativeOracle_context_wires base noQuantum N) _)
    (Native.cells base noQuantum N index)

/-- The selected physical exponent measurement and paid packing retain an
old structural read outside their measurement cells and working result. -/
lemma measured_packed_frame {shape : CShape}
    (observed : CInputRef (Native.context base noQuantum N) shape)
    (measuredSeparate : ∀ index : Fin (measurementBits N),
      (Native.cells base noQuantum N index).key ∉ observed.storageKeys)
    (workingSeparate :
      (Native.resultRef base noQuantum N).key ∉ observed.storageKeys)
    (store : Store (Native.context base noQuantum N))
    (basis : (Native.context base noQuantum N).register.Index) :
    ((measuredStore base noQuantum N store basis).applyOp
      (packing base noQuantum N)).read observed = store.read observed := by
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (packing base noQuantum N) observed workingSeparate).trans ?_
  apply Circuit.writeMeasurementPath_read_input
  intro item present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  rw [readout_key base noQuantum N index]
  exact measuredSeparate index

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
