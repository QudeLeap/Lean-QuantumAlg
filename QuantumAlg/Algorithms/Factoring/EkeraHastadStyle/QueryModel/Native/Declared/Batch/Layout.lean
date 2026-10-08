/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Slots
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained

/-!
# One original-width EH bank and fixed sample storage

The source bits, complete parameter, sixteen terminal samples and factor
result are retained before the sole original-width quantum bank. Every
later sample overwrites these same physical cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Retained source bits and complete parameter before batch storage. -/
def sourceContext : RuntimeCtx .quantum :=
  ShorStyle.Canonical.Sampler.Retained.context base N

/-- All persistent classical batch cells precede the quantum bank. -/
def storageContext : RuntimeCtx .quantum :=
  Native.Batch.Slots.context (sourceContext base N) N

include noQuantum in
theorem storage_empty : (storageContext base N).quantumWires = [] := by
  rw [storageContext, Native.Batch.Slots.nativeOracle_batchSlots_wires]
  exact noQuantum

/-- One physical bank and its working measurement/result cells serve every sample. -/
def context : RuntimeCtx .quantum :=
  Native.context (storageContext base N) (storage_empty base noQuantum N) N

/-- An earlier writable cell retains its identity under the original bank. -/
def underBank {shape : CShape} (ref : CWriteRef (storageContext base N) shape) :
    CWriteRef (context base noQuantum N) shape :=
  let bankRef : CWriteRef
      (Native.bankContext (storageContext base N) (storage_empty base noQuantum N) N) shape :=
    { toCStorageRef := ref.toCStorageRef.underOwnedLayout
        (storageContext base N).canonicalFreshKey (Native.layout N)
        (storageContext base N).canonicalFreshKey_fresh
        (Native.allocationDisjoint (storageContext base N)
          (storage_empty base noQuantum N) N)
      writable := ref.writable }
  (MeasurementCells.liftWrite 2 bankRef (measurementBits N)).underRetained
    (Native.cellsContext (storageContext base N)
      (storage_empty base noQuantum N) N).canonicalFreshKey
    (.bits (measurementBits N))
    (Native.cellsContext (storageContext base N)
      (storage_empty base noQuantum N) N).canonicalFreshKey_fresh

/-- The complete parameter is read from the original retained parameter cell. -/
def parameter : CInputRef (storageContext base N) (ParameterShape N) :=
  .storage (Native.Batch.Slots.liftWrite N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)).toCStorageRef

/-- The sampled source bits are rewritten in the same persistent cell. -/
def sourceRef : CWriteRef (context base noQuantum N) (.bits (residueSamplingBits N)) :=
  underBank base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))

/-- The recomputed parameter overwrites its original complete cell. -/
def parameterRef : CWriteRef (context base noQuantum N) (ParameterShape N) :=
  underBank base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))

/-- One actual preallocated persistent terminal slot. -/
def terminalRef (index : Fin 16) :
    CWriteRef (context base noQuantum N) (.bits (measurementBits N)) :=
  underBank base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N index)

/-- The preallocated optional factor cell receives complete classical recovery. -/
def factorRef :
    CWriteRef (context base noQuantum N) (.option (.unsignedWord (modulusBits N))) :=
  underBank base noQuantum N
    (Native.Batch.Slots.factorRef (sourceContext base N) N)

/-- The fixed batch has exactly the same original physical quantum bank. -/
theorem context_wires : (context base noQuantum N).quantumWires = (Native.layout N).wires :=
  Native.nativeOracle_context_wires
    (storageContext base N) (storage_empty base noQuantum N) N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
