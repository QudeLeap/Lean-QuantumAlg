/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Frame
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Frame

/-!
# Earlier EH samples and the parameter avoid the working measurement cells

The fixed persistent cells precede the single physical bank. Each exponent
measurement and the working pack therefore leave their values available for
the conditional joint Born law of the next sample.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A preallocated batch cell is the same structural read under the bank. -/
theorem underBank_read {shape : CShape}
    (ref : CWriteRef (storageContext base N) shape) :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (.storage ref.toCStorageRef) =
    .storage (underBank base noQuantum N ref).toCStorageRef := by
  let bankRef : CWriteRef
      (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N) shape :=
    { toCStorageRef := ref.toCStorageRef.underOwnedLayout
        (storageContext base N).canonicalFreshKey (Native.layout N)
        (storageContext base N).canonicalFreshKey_fresh
        (Native.allocationDisjoint (storageContext base N)
          (storage_empty base noQuantum N) N)
      writable := ref.writable }
  change (MeasurementCells.liftInput 2 (.storage bankRef.toCStorageRef)
    (measurementBits N)).underRetained
      (Native.cellsContext (storageContext base N)
        (storage_empty base noQuantum N) N).canonicalFreshKey
      (.bits (measurementBits N)) _ = _
  rw [MeasurementCells.liftInput_storage 2 bankRef (measurementBits N)]
  rfl

/-- Every pre-bank structural read avoids each physical measurement destination. -/
theorem lifted_measured_separate {shape : CShape}
    (observed : CInputRef (storageContext base N) shape)
    (index : Fin (measurementBits N)) :
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        observed).storageKeys := by
  let prior := MeasurementCells.liftInput 2
    (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N observed)
    (measurementBits N)
  have keys := CInputRef.storageKeys_underRetained prior
    (Native.cellsContext (storageContext base N)
      (storage_empty base noQuantum N) N).canonicalFreshKey
    (.bits (measurementBits N))
    (Native.cellsContext (storageContext base N) (storage_empty base noQuantum N)
      N).canonicalFreshKey_fresh
  exact (congrArg (fun keys =>
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉ keys)
      keys).mpr (MeasurementCells.reference_not_mem_liftInput 2
        (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N observed)
        (measurementBits N) index)

/-- Every pre-bank structural read avoids the working packed-result cell. -/
theorem lifted_working_separate {shape : CShape}
    (observed : CInputRef (storageContext base N) shape) :
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
        observed).storageKeys :=
  CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _

/-- The actual retained parameter agrees with the operand used by the query. -/
theorem parameter_read :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (parameter base N) =
        .storage (parameterRef base noQuantum N).toCStorageRef :=
  underBank_read base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))

/-- An earlier sample slot avoids each actual exponent measurement cell. -/
theorem terminal_measured_separate (written : Fin (measurementBits N))
    (index : Fin 16) :
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N written).key ∉
      (CInputRef.storage (terminalRef base noQuantum N index).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N index)
  exact (congrArg (fun read =>
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N written).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N
      (CInputRef.storage
        (Native.Batch.Slots.terminalRef (sourceContext base N) N index).toCStorageRef) written)

/-- An earlier sample slot avoids the paid working result cell. -/
theorem terminal_working_separate (index : Fin 16) :
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (terminalRef base noQuantum N index).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N index)
  exact (congrArg (fun read =>
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N
      (CInputRef.storage
        (Native.Batch.Slots.terminalRef (sourceContext base N) N index).toCStorageRef))

/-- The retained complete parameter avoids each exponent measurement cell. -/
theorem parameter_measured_separate (index : Fin (measurementBits N)) :
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (CInputRef.storage (parameterRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := parameter_read base noQuantum N
  exact (congrArg (fun read =>
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N (parameter base N) index)

/-- The retained complete parameter avoids the paid working result cell. -/
theorem parameter_working_separate :
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (parameterRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := parameter_read base noQuantum N
  exact (congrArg (fun read =>
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N (parameter base N))

/-- The retained random source avoids each exponent measurement cell. -/
theorem source_measured_separate (index : Fin (measurementBits N)) :
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      (CInputRef.storage (sourceRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact (congrArg (fun read =>
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N index).key ∉
      read.storageKeys) equal).mp
    (lifted_measured_separate base noQuantum N
      (CInputRef.storage (Native.Batch.Slots.liftWrite N
        (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)).toCStorageRef) index)

/-- The retained random source avoids the paid working result cell. -/
theorem source_working_separate :
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (CInputRef.storage (sourceRef base noQuantum N).toCStorageRef).storageKeys := by
  have equal := underBank_read base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact (congrArg (fun read =>
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      read.storageKeys) equal).mp
    (lifted_working_separate base noQuantum N
      (CInputRef.storage (Native.Batch.Slots.liftWrite N
        (ShorStyle.Canonical.Sampler.Retained.sampleRef base N)).toCStorageRef))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
