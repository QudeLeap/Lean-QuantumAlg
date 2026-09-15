/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Selection
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery.Frame
import all QuantumAlg.Components.Classical.FirstAccepted.Direct.Optional.Distribution

/-!
# Complete first-success weights in the actual original-width retry bank

The two actual selector cells form a structural observation of the current
first candidate. The source/recovery joint law preserves this observation;
the real optional selector then applies its original first-write update.
The first allocation supplies the actual empty initial value. The last real
pack writes that observation into the already consumed factor cell. These
are complete reference-weight equations for arbitrary original histories and
subnormalized states, without an independent sampler or success premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] Batch.Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private def callerLatches : CInputRef (callerContext base N)
    (.product .bit (.unsignedWord (modulusBits N))) :=
  .product (.storage (Slots.acceptedRef base (modulusBits N)).toCStorageRef)
    (.storage (Slots.selectedRef base (modulusBits N)).toCStorageRef)

/-- This structural read observes the two real persistent selection cells and executes no pack. -/
def latches : CInputRef (context base noQuantum N)
    (.product .bit (.unsignedWord (modulusBits N))) :=
  .product (.storage (selectionRefs base noQuantum N).selection.accepted.toCStorageRef)
    (.storage (selectionRefs base noQuantum N).selection.selected.toCStorageRef)

private theorem underBatch_read {shape : CShape}
    (ref : CWriteRef (callerContext base N) shape) :
    Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N
      (.storage ref.toCStorageRef) = .storage (underBatch base noQuantum N ref).toCStorageRef := by
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
    (Batch.fixedInput_storage N sourceRef)
  exact retained.trans (Batch.underBank_read (callerContext base N)
    (caller_empty base noQuantum N) N (Batch.Slots.liftWrite N sourceRef))

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
  have retained := congrArg
    (Native.liftInput (Batch.storageContext (callerContext base N) N)
      (Batch.storage_empty (callerContext base N) (caller_empty base noQuantum N) N) N)
    (Batch.fixedInput_product N firstSource secondSource)
  exact retained.trans (Batch.lifted_product (Batch.storageContext (callerContext base N) N)
    (Batch.storage_empty (callerContext base N) (caller_empty base noQuantum N) N) N
    (Batch.fixedInput N firstSource) (Batch.fixedInput N secondSource))

private theorem caller_latches :
    Batch.callerInput (callerContext base N) (caller_empty base noQuantum N) N
      (callerLatches base N) = latches base noQuantum N :=
  (caller_product base noQuantum N _ _).trans
    (congrArg₂ CInputRef.product
      (underBatch_read base noQuantum N (Slots.acceptedRef base (modulusBits N)))
      (underBatch_read base noQuantum N (Slots.selectedRef base (modulusBits N))))

private theorem latches_value (store : Store (context base noQuantum N)) :
    CShape.packOption (store.read (latches base noQuantum N)) =
      Optional.selectedValue (selectionRefs base noQuantum N).selection store := rfl

private theorem latches_separated :
    Batch.FrameSeparated (callerContext base N) (caller_empty base noQuantum N) N
      (latches base noQuantum N) :=
  (congrArg (Batch.FrameSeparated (callerContext base N) (caller_empty base noQuantum N) N)
    (caller_latches base noQuantum N)).mp
      (Batch.nativeOracle_batch_caller_separated (callerContext base N)
        (caller_empty base noQuantum N) N (callerLatches base N))

private theorem latches_factor_free :
    (factorRef base noQuantum N).key ∉ (latches base noQuantum N).storageKeys :=
  (congrArg (fun read => (factorRef base noQuantum N).key ∉ read.storageKeys)
    (caller_latches base noQuantum N)).mp
      (Batch.nativeOracle_batch_caller_factor_separate (callerContext base N)
        (caller_empty base noQuantum N) N (callerLatches base N))

attribute [local irreducible] select pack

private theorem select_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((select base noQuantum N).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (Optional.retainValue
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)
          (entry.1.read (.storage (factorRef base noQuantum N).toCStorageRef)))) left right := by
  let update := fun entry : Store (context base noQuantum N) × History =>
    ((selectionStep base noQuantum N entry.1).1,
      (entry.2, (selectionStep base noQuantum N entry.1).2))
  let observe := fun store : Store (context base noQuantum N) =>
    weight (Optional.selectedValue (selectionRefs base noQuantum N).selection store)
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        (History × (select base noQuantum N).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (nativeOracle_retrySelect_execute base noQuantum N Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) × History) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (nativeOracle_retrySelect_value base noQuantum N entry.1)

/-- Real final packing exposes exactly the selected first value, with the complete reference. -/
theorem nativeOracle_retry_pack_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((pack base noQuantum N).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (factorRef base noQuantum N).toCStorageRef))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight
          (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1))
        left right := by
  let update := fun entry : Store (context base noQuantum N) × History =>
    ((packStep base noQuantum N entry.1).1, (entry.2, (packStep base noQuantum N entry.1).2))
  let observe := fun store : Store (context base noQuantum N) =>
    weight (store.read (.storage (factorRef base noQuantum N).toCStorageRef))
  have executed := congrArg
    (fun output : State (context base noQuantum N) Reference
        (History × (pack base noQuantum N).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (nativeOracle_retryPack_execute base noQuantum N Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store (context base noQuantum N) × History) →
        (context base noQuantum N).register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (nativeOracle_retryPack_value base noQuantum N entry.1)

/-- A later actual batch and selector use the original candidate kernel with the old first value. -/
theorem nativeOracle_retry_next_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((next base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight (Optional.retainValue
              (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1) factor))
        left right := by
  let recovery := Batch.Recovery.next (callerContext base N) (caller_empty base noQuantum N) N input
  have selected := select_reference base noQuantum N (recovery.execute Reference state)
    weight left right
  have recovered := Batch.Recovery.nativeOracle_batchRecovery_next_frame_reference
    (callerContext base N) (caller_empty base noQuantum N) N input (latches base noQuantum N)
    (latches_separated base noQuantum N) (latches_factor_free base noQuantum N) state
    (fun old factor => weight (Optional.retainValue (CShape.packOption old) factor)) left right
  exact (Circuit.referenceFiberSum_execute_seq recovery (select base noQuantum N) state
    (fun store => weight (Optional.selectedValue (selectionRefs base noQuantum N).selection store))
    left right).trans (selected.trans recovered)

private theorem allocated_latches (store : Store base) :
    CShape.packOption ((Slots.pushStore base (modulusBits N) store).read (callerLatches base N)) =
      CShape.Value.optionNone := by
  change CShape.packOption (.product
    ((Slots.pushStore base (modulusBits N) store).read
      (.storage (Slots.acceptedRef base (modulusBits N)).toCStorageRef))
    ((Slots.pushStore base (modulusBits N) store).read
      (.storage (Slots.selectedRef base (modulusBits N)).toCStorageRef))) = _
  rw [(Slots.nativeOracle_retrySlots_initial base (modulusBits N) store).1]
  rfl

private theorem allocation_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Slots.allocate base (modulusBits N)).execute Reference state)
      (fun entry _ => weight (CShape.packOption (entry.1.read (callerLatches base N)))) left right =
      ExecutionState.referenceFiberSum state (fun _ _ => weight .optionNone) left right := by
  let update := fun entry : Store base × History =>
    (Slots.pushStore base (modulusBits N) entry.1, (entry.2, ((), ((), ()))))
  let observe := fun store : Store (callerContext base N) =>
    weight (CShape.packOption (store.read (callerLatches base N)))
  have executed := congrArg
    (fun output : State (callerContext base N) Reference
        (History × (Slots.allocate base (modulusBits N)).Path) =>
      ExecutionState.referenceFiberSum output (fun entry _ => observe entry.1) left right)
    (Slots.nativeOracle_retrySlots_execute base (modulusBits N) Reference state)
  refine executed.trans ((ExecutionState.referenceFiberSum_mapClassical state update
    (fun entry _ => observe entry.1) left right).trans ?_)
  apply congrArg
    (fun observe : (Store base × History) → base.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  exact congrArg weight (allocated_latches base N entry.1)

/-- Real initialization and the first batch select the original candidate on every input state. -/
theorem nativeOracle_retry_first_reference (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History)
    (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((first base noQuantum N input).execute Reference state)
      (fun entry _ => weight
        (Optional.selectedValue (selectionRefs base noQuantum N).selection entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun _ _ => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
            factor).toReal : ℂ) * weight factor) left right := by
  let allocate := Slots.allocate base (modulusBits N)
  let recovery :=
    Batch.Recovery.first (callerContext base N) (caller_empty base noQuantum N) N input
  let entered := allocate.execute Reference state
  let recoveredState := recovery.execute Reference entered
  let observe := fun store : Store (context base noQuantum N) =>
    weight (Optional.selectedValue (selectionRefs base noQuantum N).selection store)
  have selected := select_reference base noQuantum N recoveredState weight left right
  have aligned := congrArg
    (fun read : CInputRef (context base noQuantum N)
        (.product .bit (.unsignedWord (modulusBits N))) =>
      ExecutionState.referenceFiberSum recoveredState
        (fun entry _ => weight (Optional.retainValue (CShape.packOption (entry.1.read read))
          (entry.1.read (.storage (factorRef base noQuantum N).toCStorageRef)))) left right)
    (caller_latches base noQuantum N)
  have recovered := Batch.Recovery.nativeOracle_batchRecovery_first_frame_reference
    (callerContext base N) (caller_empty base noQuantum N) N input (callerLatches base N) entered
    (fun old factor => weight (Optional.retainValue (CShape.packOption old) factor)) left right
  have initialized := allocation_reference base N state
    (fun old => ∑ factor : (LatticeBatchRecoveryOutput.OutputShape N).Value,
      ((((sampledBatchOutputPMF input).map LatticeBatchRecoveryOutput.outputValue)
        factor).toReal : ℂ) * weight (Optional.retainValue old factor)) left right
  exact (Circuit.referenceFiberSum_execute_seq allocate (recovery.seq (select base noQuantum N))
    state observe left right).trans
      ((Circuit.referenceFiberSum_execute_seq recovery (select base noQuantum N)
        entered observe left right).trans
          (selected.trans (aligned.symm.trans (recovered.trans initialized))))


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry
