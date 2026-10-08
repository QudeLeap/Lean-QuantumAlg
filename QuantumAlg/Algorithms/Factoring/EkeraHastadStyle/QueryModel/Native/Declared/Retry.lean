/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Slots
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Allocation

/-!
# First-success primitives on one declared EH bank

The selector cells precede the source and the sole quantum bank. The first
and reused batch primitives perform complete recovery and optional selection.
The paid pack writes the selected factor into the consumed result cell.
The completed finite execution composes these primitives with a physical
bank reset after each batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Persistent selector cells are allocated before the source and bank. -/
def callerContext : RuntimeCtx .quantum :=
  Native.Retry.Slots.context base (modulusBits N)

include noQuantum in
private theorem caller_empty : (callerContext base N).quantumWires = [] :=
  (Native.Retry.Slots.nativeOracle_retrySlots_wires base (modulusBits N)).trans noQuantum

/-- All positive retry rounds share this one full bank and storage context. -/
def context : RuntimeCtx .quantum :=
  Batch.context (callerContext base N)
    (caller_empty base noQuantum N) N

/-- Lift an earlier selector cell under the source, samples and quantum bank. -/
def underBatch {shape : CShape}
    (ref : CWriteRef (callerContext base N) shape) :
    CWriteRef (context base noQuantum N) shape :=
  let sourceRef := (ref.underRetained (callerContext base N).canonicalFreshKey
    (.bits (residueSamplingBits N))
    (callerContext base N).canonicalFreshKey_fresh).underRetained
      (ShorStyle.Canonical.Sampler.Retained.sampleContext
        (callerContext base N) N).canonicalFreshKey
      (ParameterShape N)
      (ShorStyle.Canonical.Sampler.Retained.sampleContext
        (callerContext base N) N).canonicalFreshKey_fresh
  Batch.underBank (callerContext base N)
    (caller_empty base noQuantum N) N
    (Native.Batch.Slots.liftWrite N sourceRef)

/-- The selector addresses precisely the three preallocated persistent cells. -/
def selectionRefs : Optional.Refs (context base noQuantum N) (modulusBits N) where
  selection :=
    ⟨underBatch base noQuantum N
      (Native.Retry.Slots.acceptedRef base (modulusBits N)),
     underBatch base noQuantum N
      (Native.Retry.Slots.selectedRef base (modulusBits N))⟩
  unpacked := underBatch base noQuantum N
    (Native.Retry.Slots.unpackedRef base (modulusBits N))

/-- The actual batch factor cell doubles as the final selected destination. -/
def factorRef : CWriteRef (context base noQuantum N)
    (.option (.unsignedWord (modulusBits N))) :=
  Batch.factorRef (callerContext base N)
    (caller_empty base noQuantum N) N

/-- Decode each actual candidate before the stored first-success selection. -/
def select : Circuit (model input) (context base noQuantum N)
    (context base noQuantum N) :=
  Optional.into (model := model input)
    (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N)

/-- The first complete recovery is followed immediately by real selection. -/
def first : Circuit (model input) base (context base noQuantum N) :=
  .seq (Native.Retry.Slots.allocate (model := model input) base (modulusBits N))
    (.seq (Batch.Recovery.first (callerContext base N)
      (caller_empty base noQuantum N) N input)
      (select base noQuantum N input))

/-- Every later batch redraws, reuses the same bank and selects in place. -/
def next : Circuit (model input) (context base noQuantum N)
    (context base noQuantum N) :=
  .seq (Batch.Recovery.next (callerContext base N)
    (caller_empty base noQuantum N) N input)
    (select base noQuantum N input)

/-- Final packing overwrites the consumed candidate cell with the selected value. -/
def pack : Circuit (model input) (context base noQuantum N)
    (context base noQuantum N) :=
  BitWord.instruction (execution := model input)
    (Optional.Allocation.packOp (selectionRefs base noQuantum N)
      (factorRef base noQuantum N))

/-- The retry retains precisely the one original-width physical bank. -/
theorem context_wires :
    (context base noQuantum N).quantumWires = (Native.layout N).wires :=
  Batch.context_wires (callerContext base N)
    (caller_empty base noQuantum N) N

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
