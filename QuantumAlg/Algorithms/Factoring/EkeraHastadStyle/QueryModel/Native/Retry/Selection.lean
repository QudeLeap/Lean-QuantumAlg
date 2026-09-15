/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Slots.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.State

/-!
# Actual first-success selection and final packing in the fixed oracle bank

The selector uses three genuinely distinct cells allocated before the bank.
Its complete state equation is the original optional-unpack and direct
selector record. The final paid pack writes into the already consumed
candidate cell. These are statements about actual stores and paths, without
a sampling distribution, success premise or hidden output allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem liftedSamples_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (width : Nat) (ref : CWriteRef ctx shape) (count : Nat) :
    (Batch.Slots.liftSamples width ref count).key = ref.key := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

attribute [local irreducible] Batch.Slots.samples Batch.Slots.liftSamples

private theorem liftedWrite_key {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (N : Nat) (ref : CWriteRef ctx shape) : (Batch.Slots.liftWrite N ref).key = ref.key :=
  liftedSamples_key (measurementBits N) ref 16

attribute [local irreducible] Batch.Slots.liftWrite

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- All real source, sample and bank extensions preserve an earlier selector key. -/
theorem nativeOracle_retry_underBatch_key {shape : CShape}
    (ref : CWriteRef (callerContext base N) shape) :
    (underBatch base noQuantum N ref).key = ref.key := by
  let sourceRef : CWriteRef (Batch.sourceContext (callerContext base N) N) shape :=
    (ref.underRetained (callerContext base N).canonicalFreshKey
      (.bits (residueSamplingBits N)) (callerContext base N).canonicalFreshKey_fresh).underRetained
        (ShorStyle.Canonical.Sampler.Retained.sampleContext
          (callerContext base N) N).canonicalFreshKey (ParameterShape N)
        (ShorStyle.Canonical.Sampler.Retained.sampleContext
          (callerContext base N) N).canonicalFreshKey_fresh
  change (Batch.underBank (callerContext base N) (caller_empty base noQuantum N) N
    (Batch.Slots.liftWrite N sourceRef)).key = ref.key
  have sourceKey : sourceRef.key = ref.key := rfl
  have samplesKey : (Batch.Slots.liftWrite N sourceRef).key = ref.key :=
    (liftedWrite_key N sourceRef).trans sourceKey
  exact (Batch.nativeOracle_underBank_key (callerContext base N) (caller_empty base noQuantum N) N
    (Batch.Slots.liftWrite N sourceRef)).trans samplesKey

/-- Actual fresh allocation establishes the existing optional selector's full separation. -/
theorem nativeOracle_retry_selection_separated :
    Optional.Separation (selectionRefs base noQuantum N) := by
  have keys := Slots.nativeOracle_retrySlots_keys base (modulusBits N)
  constructor
  · intro same
    exact keys.1 ((nativeOracle_retry_underBatch_key base noQuantum N _).symm.trans
      (same.trans (nativeOracle_retry_underBatch_key base noQuantum N _)))
  · intro same
    exact keys.2.1 ((nativeOracle_retry_underBatch_key base noQuantum N _).symm.trans
      (same.trans (nativeOracle_retry_underBatch_key base noQuantum N _)))
  · intro same
    exact keys.2.2 ((nativeOracle_retry_underBatch_key base noQuantum N _).symm.trans
      (same.trans (nativeOracle_retry_underBatch_key base noQuantum N _)))

/-- This is the existing selector's actual full store and branch record. -/
def selectionStep (store : Store (context base noQuantum N)) :
    Store (context base noQuantum N) × (select base noQuantum N).Path :=
  Optional.step (.storage (factorRef base noQuantum N).toCStorageRef)
    (selectionRefs base noQuantum N) store

/-- Unpacking and selection preserve every complete reference block and the actual history. -/
theorem nativeOracle_retrySelect_execute (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (select base noQuantum N).execute Reference state = state.mapClassical (fun entry =>
      ((selectionStep base noQuantum N entry.1).1,
        (entry.2, (selectionStep base noQuantum N entry.1).2))) :=
  Optional.into_execute _ _ Reference state

/-- The actual update keeps the first populated candidate and uses the same current factor read. -/
theorem nativeOracle_retrySelect_value (store : Store (context base noQuantum N)) :
    Optional.selectedValue (selectionRefs base noQuantum N).selection
        (selectionStep base noQuantum N store).1 =
      Optional.retainValue (Optional.selectedValue
        (selectionRefs base noQuantum N).selection store)
        (store.read (.storage (factorRef base noQuantum N).toCStorageRef)) :=
  Optional.into_correct _ _ (nativeOracle_retry_selection_separated base noQuantum N) store

/-- Every earlier read outside the three actual selector writes is preserved. -/
theorem nativeOracle_retrySelect_frame (store : Store (context base noQuantum N))
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (acceptedFree : (selectionRefs base noQuantum N).selection.accepted.key ∉ observed.storageKeys)
    (selectedFree : (selectionRefs base noQuantum N).selection.selected.key ∉ observed.storageKeys)
    (unpackedFree : (selectionRefs base noQuantum N).unpacked.key ∉ observed.storageKeys) :
    (selectionStep base noQuantum N store).1.read observed = store.read observed :=
  Optional.into_callerFrame _ _ store observed acceptedFree selectedFree unpackedFree

/-- The real final pack writes precisely the selected value into the existing factor cell. -/
def packStep (store : Store (context base noQuantum N)) :
    Store (context base noQuantum N) × (pack base noQuantum N).Path :=
  (store.applyOp (Optional.Allocation.packOp (selectionRefs base noQuantum N)
    (factorRef base noQuantum N)), ())

/-- Complete final-pack execution records its actual instruction and retains all correlations. -/
theorem nativeOracle_retryPack_execute (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History) :
    (pack base noQuantum N).execute Reference state = state.mapClassical (fun entry =>
      ((packStep base noQuantum N entry.1).1,
        (entry.2, (packStep base noQuantum N entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical
    (Optional.Allocation.packOp (selectionRefs base noQuantum N) (factorRef base noQuantum N))
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The same actual declared result read returns the first accepted value after its paid pack. -/
theorem nativeOracle_retryPack_value (store : Store (context base noQuantum N)) :
    (packStep base noQuantum N store).1.read
        (.storage (factorRef base noQuantum N).toCStorageRef) =
      Optional.selectedValue (selectionRefs base noQuantum N).selection store :=
  Store.read_applyOp_output store _

/-- Final packing changes only the consumed candidate/result destination. -/
theorem nativeOracle_retryPack_frame (store : Store (context base noQuantum N))
    {shape : CShape} (observed : CInputRef (context base noQuantum N) shape)
    (separate : (factorRef base noQuantum N).key ∉ observed.storageKeys) :
    (packStep base noQuantum N store).1.read observed = store.read observed :=
  Store.read_applyOp_of_not_mem_storageKeys store _ observed separate

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
