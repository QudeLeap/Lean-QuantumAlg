/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Slots
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation

/-!
# Actual first-success retry on the original fixed oracle bank

The three selector cells are retained before the sole source-and-bank setup.
Every requested batch really runs, including batches after the first success.
Each original recovery is followed immediately by the existing optional
unpack and direct first-success selector. Subsequent batches redraw and pay
for reset while reusing the same sample, parameter and factor cells.

After the final selection, one paid pack writes the first accepted value
back into the now-consumed factor cell. The complete output lists that same
bank and all actual retained classical storage. This positive-count
constructor asserts no independent sampling or legacy resource equality.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The persistent selector is allocated before any sample source or quantum bank. -/
def callerContext : RuntimeCtx .quantum := Slots.context base (modulusBits N)

include noQuantum in
private theorem caller_empty : (callerContext base N).quantumWires = [] :=
  (Slots.nativeOracle_retrySlots_wires base (modulusBits N)).trans noQuantum

/-- Every positive retry uses one fixed complete bank-and-storage context. -/
def context : RuntimeCtx .quantum :=
  Batch.context (callerContext base N) (caller_empty base noQuantum N) N

/-- Lift a real earlier writable selector cell beneath the source, slots and original bank. -/
def underBatch {shape : CShape} (ref : CWriteRef (callerContext base N) shape) :
    CWriteRef (context base noQuantum N) shape :=
  let sourceRef := (ref.underRetained (callerContext base N).canonicalFreshKey
    (.bits (residueSamplingBits N)) (callerContext base N).canonicalFreshKey_fresh).underRetained
      (ShorStyle.Canonical.Sampler.Retained.sampleContext
        (callerContext base N) N).canonicalFreshKey
      (ParameterShape N)
      (ShorStyle.Canonical.Sampler.Retained.sampleContext
        (callerContext base N) N).canonicalFreshKey_fresh
  Batch.underBank (callerContext base N) (caller_empty base noQuantum N) N
    (Batch.Slots.liftWrite N sourceRef)

/-- The existing selector reads and writes exactly the three actual persistent cells. -/
def selectionRefs : Optional.Refs (context base noQuantum N) (modulusBits N) where
  selection :=
    ⟨underBatch base noQuantum N (Slots.acceptedRef base (modulusBits N)),
      underBatch base noQuantum N (Slots.selectedRef base (modulusBits N))⟩
  unpacked := underBatch base noQuantum N (Slots.unpackedRef base (modulusBits N))

/-- This is the existing batch factor cell, used for candidates and the final selected output. -/
def factorRef :
    CWriteRef (context base noQuantum N) (.option (.unsignedWord (modulusBits N))) :=
  Batch.factorRef (callerContext base N) (caller_empty base noQuantum N) N

/-- Actual optional decoding precedes the original direct first-success selector. -/
def select : Circuit (context base noQuantum N) (context base noQuantum N) :=
  Optional.into (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N)

/-- The first actual source draw, sixteen samples and recovery precede the first selection. -/
def first (input : Input N) : Circuit base (context base noQuantum N) :=
  .seq (Slots.allocate base (modulusBits N))
    (.seq (Batch.Recovery.first (callerContext base N) (caller_empty base noQuantum N) N input)
      (select base noQuantum N))

/-- Each later actual batch and selection overwrites the same fixed working destinations. -/
def next (input : Input N) : Circuit (context base noQuantum N) (context base noQuantum N) :=
  .seq (Batch.Recovery.next (callerContext base N) (caller_empty base noQuantum N) N input)
    (select base noQuantum N)

/-- One actual final pack reuses the consumed candidate cell as the declared result. -/
def pack : Circuit (context base noQuantum N) (context base noQuantum N) :=
  .classical (Optional.Allocation.packOp (selectionRefs base noQuantum N)
    (factorRef base noQuantum N))

/-- Execute one first batch and exactly the requested number of real later batches. -/
def code (input : Input N) (laterCount : Nat) : Circuit base (context base noQuantum N) :=
  .seq (first base noQuantum N input)
    (.seq (Circuit.forRange laterCount (fun _ => next base noQuantum N input))
      (pack base noQuantum N))

/-- The actual first-success output retains every surviving selector, sample cell and wire. -/
def run (input : Input N) (laterCount : Nat) :
    AlgorithmRun base (context base noQuantum N) (.option (.unsignedWord (modulusBits N))) where
  code := code base noQuantum N input laterCount
  output := Output.all (context base noQuantum N)
    (.read (.storage (factorRef base noQuantum N).toCStorageRef))

/-- The repeated execution still has exactly the original oracle's single physical bank. -/
theorem nativeOracle_retry_wires : (context base noQuantum N).quantumWires = (layout N).wires :=
  Batch.nativeOracle_batch_wires (callerContext base N) (caller_empty base noQuantum N) N

/-- No actual live storage or quantum subsystem is hidden from the positive retry output. -/
theorem nativeOracle_retry_output_listing (input : Input N) (laterCount : Nat) :
    (run base noQuantum N input laterCount).output.listing = (context base noQuantum N).keys := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
