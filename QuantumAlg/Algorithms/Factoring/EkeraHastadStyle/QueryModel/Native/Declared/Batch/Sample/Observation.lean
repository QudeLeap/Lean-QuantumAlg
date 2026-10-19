/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Outcome
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame

/-!
# Actual EH batch slot agrees with the declared measured exponent outcome

The first paid pack produces the working result, and the second paid pack
copies the same finite measured cells into one persistent sample slot. Their
physical writes therefore encode the same short-DLP source readout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat)

private lemma copiedValue_packing (store : Store (context base noQuantum N)) :
    copiedValue base noQuantum N
      (store.applyOp (Declared.packing (storageContext base N)
        (storage_empty base noQuantum N) N)) =
      copiedValue base noQuantum N store := by
  apply congrArg (CShape.packFiniteBits (measurementBits N))
  apply Store.read_applyOp_of_not_mem_storageKeys
  exact CInputRef.fresh_not_mem_storageKeys_underRetained
    (.fixedVector fun index => .storage
      (MeasurementCells.reference
        (Native.bankContext (storageContext base N)
          (storage_empty base noQuantum N) N)
        2 (measurementBits N) index).toCStorageRef) _ _ _

private lemma copiedValue_result (store : Store (context base noQuantum N)) :
    copiedValue base noQuantum N store =
      (store.applyOp (Declared.packing (storageContext base N)
        (storage_empty base noQuantum N) N)).read
          (.storage (Native.resultRef (storageContext base N)
            (storage_empty base noQuantum N) N).toCStorageRef) := by
  exact (Store.read_applyOp_output store
    (Declared.packing (storageContext base N)
      (storage_empty base noQuantum N) N)).symm

/-- Packing the real measurement cells gives the same word in the working
result cell and in the second pack's source read. -/
lemma copiedValue_packed_result (store : Store (context base noQuantum N)) :
    copiedValue base noQuantum N
      (store.applyOp (Declared.packing (storageContext base N)
        (storage_empty base noQuantum N) N)) =
      (store.applyOp (Declared.packing (storageContext base N)
        (storage_empty base noQuantum N) N)).read
          (.storage (Native.resultRef (storageContext base N)
            (storage_empty base noQuantum N) N).toCStorageRef) :=
  (copiedValue_packing base noQuantum N store).trans
    (copiedValue_result base noQuantum N store)

/-- The actual stored sample slot contains exactly the short-DLP readout
of the same physical exponent measurement. -/
lemma copied_outcome (index : Fin 16)
    (store : Store (context base noQuantum N))
    (basis : (context base noQuantum N).register.Index) :
    (copyStep base noQuantum N index
      ((Declared.measuredStore (storageContext base N)
        (storage_empty base noQuantum N) N store basis).applyOp
          (Declared.packing (storageContext base N)
            (storage_empty base noQuantum N) N))).1.read
      (.storage (terminalRef base noQuantum N index).toCStorageRef) =
      CShape.Value.bits ((ShortDLP.measurement (Native.parameters N)).readout
        (Native.basisEquiv N
          (Native.nativeOracle_context_wires (storageContext base N)
            (storage_empty base noQuantum N) N) basis)) := by
  let measured : Store (context base noQuantum N) :=
    Declared.measuredStore (storageContext base N)
    (storage_empty base noQuantum N) N store basis
  let packed : Store (context base noQuantum N) := measured.applyOp
    (Declared.packing (storageContext base N) (storage_empty base noQuantum N) N)
  change (copyStep base noQuantum N index packed).1.read
    (.storage (terminalRef base noQuantum N index).toCStorageRef) = _
  rw [copy_read base noQuantum N index packed]
  rw [copiedValue_packing base noQuantum N measured]
  rw [copiedValue_result base noQuantum N measured]
  exact Declared.packed_output (storageContext base N)
    (storage_empty base noQuantum N) N store basis

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
