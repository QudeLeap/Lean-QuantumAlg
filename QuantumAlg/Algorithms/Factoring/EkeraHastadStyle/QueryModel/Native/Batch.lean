/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Slots
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Reuse
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Sixteen actual original-width samples in one fixed context

The actual residue draw and parameter computation come first. Sixteen sample
slots and one factor result are then retained, before preparing the only
quantum bank. The first member uses that preparation; the other fifteen pay
for reset on the same physical bank. Each member also executes a second real
finite-bit pack into its persistent slot. The original working packed result
remains live and contributes an additional measurement-width bit string.

A subsequent batch redraws the source and recomputes the parameter in their
existing cells, then performs sixteen paid reset/member/pack sequences. Its
entire circuit has the same input and output context, with no reallocation,
context cast, or new quantum bank.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The original source draw and complete parameter have their own retained cells. -/
def sourceContext : RuntimeCtx .quantum := ShorStyle.Canonical.Sampler.Retained.context base N

/-- Fix every persistent classical batch cell before preparing the one quantum bank. -/
def storageContext : RuntimeCtx .quantum := Slots.context (sourceContext base N) N

include noQuantum in
private theorem storage_empty : (storageContext base N).quantumWires = [] := by
  rw [storageContext, Slots.nativeOracle_batchSlots_wires]
  exact noQuantum

/-- The same actual bank, measurement cells and working packed result serve every member. -/
def context : RuntimeCtx .quantum :=
  Native.context (storageContext base N) (storage_empty base noQuantum N) N

/-- A writable cell retains its identity under the actual bank and result allocations. -/
def underBank {shape : CShape} (ref : CWriteRef (storageContext base N) shape) :
    CWriteRef (context base noQuantum N) shape :=
  let bankRef : CWriteRef
      (bankContext (storageContext base N) (storage_empty base noQuantum N) N) shape :=
    { toCStorageRef := ref.toCStorageRef.underOwnedLayout
        (storageContext base N).canonicalFreshKey (layout N)
        (storageContext base N).canonicalFreshKey_fresh
        (allocationDisjoint (storageContext base N) (storage_empty base noQuantum N) N)
      writable := ref.writable }
  (MeasurementCells.liftWrite 2 bankRef (measurementBits N)).underRetained
    (cellsContext (storageContext base N) (storage_empty base noQuantum N) N).canonicalFreshKey
    (.bits (measurementBits N))
    (cellsContext (storageContext base N)
      (storage_empty base noQuantum N) N).canonicalFreshKey_fresh

/-- The complete stored parameter is lifted structurally before quantum preparation. -/
def parameter : CInputRef (storageContext base N) (ParameterShape N) :=
  .storage (Slots.liftWrite N
    (ShorStyle.Canonical.Sampler.Retained.parameterRef base N)).toCStorageRef

/-- The source random bits are rewritten in the same retained cell for later batches. -/
def sourceRef : CWriteRef (context base noQuantum N) (.bits (residueSamplingBits N)) :=
  underBank base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))

/-- Later parameter computation writes the same complete retained parameter. -/
def parameterRef : CWriteRef (context base noQuantum N) (ParameterShape N) :=
  underBank base noQuantum N
    (Slots.liftWrite N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))

/-- Every terminal points to one preallocated sample cell beside the same bank. -/
def terminalRef (index : Fin 16) :
    CWriteRef (context base noQuantum N) (.bits (measurementBits N)) :=
  underBank base noQuantum N (Slots.terminalRef (sourceContext base N) N index)

/-- Recovery will write its original optional factor into this actual preallocated cell. -/
def factorRef : CWriteRef (context base noQuantum N) (.option (.unsignedWord (modulusBits N))) :=
  underBank base noQuantum N (Slots.factorRef (sourceContext base N) N)

/-- One extra actual pack copies the measured finite cells into the selected persistent slot. -/
def copy (index : Fin 16) : Circuit (context base noQuantum N) (context base noQuantum N) :=
  .classical (.packFiniteBits (measurementBits N) (context base noQuantum N)
    (.fixedVector fun position =>
      .storage (cells (storageContext base N) (storage_empty base noQuantum N) N
        position).toCStorageRef)
    (terminalRef base noQuantum N index))

/-- A subsequent sample resets, executes the same original member and writes its actual slot. -/
def reusedSample (input : Input N) (index : Fin 16) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (reuse (storageContext base N) (storage_empty base noQuantum N) N input (parameter base N))
    (copy base noQuantum N index)

/-- The first sample consumes real preparation; all fifteen successors pay for reset. -/
def firstBatch (input : Input N) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq
    (.seq (body (storageContext base N) (storage_empty base noQuantum N) N
      input (parameter base N)) (copy base noQuantum N 0))
    (Circuit.forRange 15 fun index => reusedSample base noQuantum N input index.succ)

/-- Draw a fresh actual source and recompute the full parameter in the existing two cells. -/
def redraw : Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (ShorStyle.Canonical.Sampler.PackedSample.draw N (sourceRef base noQuantum N))
    (ShorStyle.Canonical.Sampler.Program.circuit N
      (.storage (sourceRef base noQuantum N).toCStorageRef) (parameterRef base noQuantum N))

/-- Later batches keep the same context and perform sixteen real reset/member/pack sequences. -/
def nextBatch (input : Input N) :
    Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (redraw base noQuantum N)
    (Circuit.forRange 16 (reusedSample base noQuantum N input))

/-- The real source draw precedes all fixed slots and the single actual bank preparation. -/
def setup : Circuit base (context base noQuantum N) :=
  .seq (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (.seq (Slots.allocate (sourceContext base N) N)
      (.seq (prepare (storageContext base N) (storage_empty base noQuantum N) N)
        (allocate (storageContext base N) (storage_empty base noQuantum N) N)))

/-- Run the complete first batch on the actual retained parameter and fixed terminal cells. -/
def code (input : Input N) : Circuit base (context base noQuantum N) :=
  .seq (setup base noQuantum N) (firstBatch base noQuantum N input)

/-- All sixteen outputs are actual reads, and every other surviving entry remains listed. -/
def run (input : Input N) :
    AlgorithmRun base (context base noQuantum N) (.fixedVector 16 (.bits (measurementBits N))) where
  code := code base noQuantum N input
  output := Output.all (context base noQuantum N)
    (.read (.fixedVector fun index =>
      .storage (terminalRef base noQuantum N index).toCStorageRef))

/-- The fixed batch retains exactly the original oracle's physical bank. -/
theorem nativeOracle_batch_wires : (context base noQuantum N).quantumWires = (layout N).wires :=
  nativeOracle_context_wires (storageContext base N) (storage_empty base noQuantum N) N

/-- No sample slot, source parameter, working result or quantum wire is hidden from the output. -/
theorem nativeOracle_batch_output_listing (input : Input N) :
    (run base noQuantum N input).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch
