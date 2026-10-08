/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Selection
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Caller

/-!
# Original EH selector read under the physical batch

The actual accepted bit and selected word are allocated before the source
and quantum bank. Their structural read under all later allocations is
exactly the selector read used by the paid update.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Read the two persistent selector cells before physical batch allocation. -/
def originalSelectionInput : CInputRef (callerContext base N)
    (.product .bit (.unsignedWord (modulusBits N))) :=
  .product
    (.storage (Native.Retry.Slots.acceptedRef base (modulusBits N)).toCStorageRef)
    (.storage (Native.Retry.Slots.selectedRef base (modulusBits N)).toCStorageRef)

/-- Read the same two cells at their real addresses in the complete bank. -/
def selectionInput : CInputRef (context base noQuantum N)
    (.product .bit (.unsignedWord (modulusBits N))) :=
  .product
    (.storage (selectionRefs base noQuantum N).selection.accepted.toCStorageRef)
    (.storage (selectionRefs base noQuantum N).selection.selected.toCStorageRef)

private theorem caller_storage {shape : CShape}
    (ref : CWriteRef (callerContext base N) shape) :
    Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N
      (.storage ref.toCStorageRef) =
      .storage (underBatch base noQuantum N ref).toCStorageRef := by
  let sourceRef : CWriteRef (Batch.sourceContext (callerContext base N) N) shape :=
    (ref.underRetained (callerContext base N).canonicalFreshKey
      (.bits (residueSamplingBits N)) (callerContext base N).canonicalFreshKey_fresh).underRetained
        (ShorStyle.Canonical.Sampler.Retained.sampleContext
          (callerContext base N) N).canonicalFreshKey (ParameterShape N)
        (ShorStyle.Canonical.Sampler.Retained.sampleContext
          (callerContext base N) N).canonicalFreshKey_fresh
  have retained := congrArg
    (Native.liftInput (Batch.storageContext (callerContext base N) N)
      (Batch.storage_empty (callerContext base N) (caller_empty base noQuantum N) N) N)
    (Batch.fixedInput_storage (callerContext base N) N sourceRef)
  exact retained.trans (Batch.underBank_read (callerContext base N)
    (caller_empty base noQuantum N) N (Native.Batch.Slots.liftWrite N sourceRef))

private theorem caller_product {left right : CShape}
    (first : CInputRef (callerContext base N) left)
    (second : CInputRef (callerContext base N) right) :
    Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N
      (.product first second) =
      .product
        (Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N first)
        (Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N second) := by
  let firstSource := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) first
  let secondSource := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) second
  have fixed := congrArg
    (Native.liftInput (Batch.storageContext (callerContext base N) N)
      (Batch.storage_empty (callerContext base N) (caller_empty base noQuantum N) N) N)
    (Batch.fixedInput_product (callerContext base N) N firstSource secondSource)
  exact fixed.trans (Batch.lifted_product (callerContext base N)
    (caller_empty base noQuantum N) N
    (Batch.fixedInput (callerContext base N) N firstSource)
    (Batch.fixedInput (callerContext base N) N secondSource))

/-- The batch's original-caller read is precisely the actual selector pair. -/
theorem caller_selectionInput :
    Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N
      (originalSelectionInput base N) = selectionInput base noQuantum N := by
  exact (caller_product base noQuantum N _ _).trans
    (congrArg₂ CInputRef.product
      (caller_storage base noQuantum N
        (Native.Retry.Slots.acceptedRef base (modulusBits N)))
      (caller_storage base noQuantum N
        (Native.Retry.Slots.selectedRef base (modulusBits N))))

/-- First-success selection reads exactly the preserved selector pair. -/
theorem selectedValue_selectionInput
    (store : Store (context base noQuantum N)) :
    Optional.selectedValue (selectionRefs base noQuantum N).selection store =
      CShape.packOption (store.read (selectionInput base noQuantum N)) := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry
