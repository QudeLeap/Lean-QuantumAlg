/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Frame
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Sample.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Slots.Reference
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# Earlier caller reads under the declared EH bank

The actual source, sixteen sample cells, factor cell, owned quantum bank and
measurement cells retain the identity of every original caller storage key.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Lift one earlier read under the sixteen sample cells and factor cell. -/
def fixedInput {shape : CShape} (observed : CInputRef (sourceContext base N) shape) :
    CInputRef (storageContext base N) shape :=
  (Native.Batch.Slots.slotsInput (measurementBits N) observed 16).underRetained
    (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16).canonicalFreshKey
    (.option (.unsignedWord (modulusBits N)))
    (Native.Batch.Slots.samples (sourceContext base N)
      (measurementBits N) 16).canonicalFreshKey_fresh

/-- The exact structural read of one prior caller value below every physical allocation. -/
def callerInput {shape : CShape} (observed : CInputRef base shape) :
    CInputRef (context base noQuantum N) shape :=
  Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
    (fixedInput base N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed))

private theorem slotsInput_keys {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (observed : CInputRef ctx shape) (count : Nat) :
    (Native.Batch.Slots.slotsInput width observed count).storageKeys =
      observed.storageKeys := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (CInputRef.storageKeys_underRetained _ _ _ _).trans ih

private theorem fixedInput_keys {shape : CShape}
    (observed : CInputRef (sourceContext base N) shape) :
    (fixedInput base N observed).storageKeys = observed.storageKeys :=
  (CInputRef.storageKeys_underRetained _ _ _ _).trans
    (slotsInput_keys (measurementBits N) observed 16)

private theorem bankInput_keys {ctx : RuntimeCtx .quantum} (noQuantum : ctx.quantumWires = [])
    (N : Nat) {shape : CShape} (observed : CInputRef ctx shape) :
    (Native.bankInput ctx noQuantum N observed).storageKeys = observed.storageKeys := by
  induction observed with
  | storage ref => rfl
  | product first second firstIH secondIH => exact congrArg₂ List.append firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg List.flatten (congrArg List.ofFn (funext entriesIH))
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

private theorem nativeInput_keys {ctx : RuntimeCtx .quantum} (noQuantum : ctx.quantumWires = [])
    (N : Nat) {shape : CShape} (observed : CInputRef ctx shape) :
    (Native.liftInput ctx noQuantum N observed).storageKeys = observed.storageKeys :=
  (CInputRef.storageKeys_underRetained _ _ _ _).trans
    ((MeasurementCells.liftInput_storageKeys 2 (Native.bankInput ctx noQuantum N observed)
      (measurementBits N)).trans (bankInput_keys noQuantum N observed))

/-- A caller read has exactly its earlier storage keys under the whole bank. -/
theorem callerInput_keys {shape : CShape} (observed : CInputRef base shape) :
    (callerInput base noQuantum N observed).storageKeys = observed.storageKeys := by
  have sourceKeys :
      (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed).storageKeys =
        observed.storageKeys :=
    (CInputRef.storageKeys_underRetained _ _ _ _).trans
      (CInputRef.storageKeys_underRetained _ _ _ _)
  exact (nativeInput_keys (storage_empty base noQuantum N) N
    (fixedInput base N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed))).trans
      ((fixedInput_keys base N _).trans sourceKeys)

private theorem sample_not_mem_input {ctx : RuntimeCtx .quantum} {shape : CShape}
    (width : Nat) (observed : CInputRef ctx shape) (count : Nat) (index : Fin count) :
    (Native.Batch.Slots.sampleRef ctx width count index).key ∉
      (Native.Batch.Slots.slotsInput width observed count).storageKeys := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun previous => ?_) index
      · exact CInputRef.fresh_not_mem_storageKeys_underRetained
          (Native.Batch.Slots.slotsInput width observed count)
          (Native.Batch.Slots.samples ctx width count).canonicalFreshKey
          (.bits width) (Native.Batch.Slots.samples ctx width count).canonicalFreshKey_fresh
      · change (Native.Batch.Slots.sampleRef ctx width count previous).key ∉
          ((Native.Batch.Slots.slotsInput width observed count).underRetained
            (Native.Batch.Slots.samples ctx width count).canonicalFreshKey (.bits width)
            (Native.Batch.Slots.samples ctx width count).canonicalFreshKey_fresh).storageKeys
        rw [CInputRef.storageKeys_underRetained]
        exact ih previous

attribute [local irreducible] Native.Batch.Slots.samples

/-- Every original caller read avoids each actual retained sample destination. -/
theorem caller_slot_separated {shape : CShape}
    (observed : CInputRef base shape) (index : Fin 16) :
    (terminalRef base noQuantum N index).key ∉
      (callerInput base noQuantum N observed).storageKeys := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  have finalKeys : (callerInput base noQuantum N observed).storageKeys =
      sourceInput.storageKeys :=
    (nativeInput_keys (storage_empty base noQuantum N) N
      (fixedInput base N sourceInput)).trans (fixedInput_keys base N sourceInput)
  have oldAbsent := sample_not_mem_input (measurementBits N) sourceInput 16 index
  have oldKeys := slotsInput_keys (measurementBits N) sourceInput 16
  have oldResult :
      (Native.Batch.Slots.terminalRef (sourceContext base N) N index).key ∉
        sourceInput.storageKeys :=
    (congrArg (fun keys =>
      (Native.Batch.Slots.sampleRef (sourceContext base N)
        (measurementBits N) 16 index).key ∉ keys) oldKeys).mp oldAbsent
  exact (congrArg₂ (fun key keys => key ∉ keys)
    (underBank_key base noQuantum N
      (Native.Batch.Slots.terminalRef (sourceContext base N) N index)) finalKeys).mpr oldResult

/-- Every original caller read avoids all physical measurement destinations. -/
theorem caller_measured_separated {shape : CShape}
    (observed : CInputRef base shape) (position : Fin (measurementBits N)) :
    (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
      (callerInput base noQuantum N observed).storageKeys :=
  lifted_measured_separate base noQuantum N
    (fixedInput base N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed))
    position

/-- Every original caller read avoids the working packed-result destination. -/
theorem caller_working_separated {shape : CShape}
    (observed : CInputRef base shape) :
    (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
      (callerInput base noQuantum N observed).storageKeys :=
  lifted_working_separate base noQuantum N
    (fixedInput base N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed))

theorem fixedInput_storage {shape : CShape}
    (ref : CWriteRef (sourceContext base N) shape) :
    fixedInput base N (.storage ref.toCStorageRef) =
      .storage (Native.Batch.Slots.liftWrite N ref).toCStorageRef :=
  congrArg
    (fun read : CInputRef
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16) shape =>
      read.underRetained
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Native.Batch.Slots.samples (sourceContext base N)
          (measurementBits N) 16).canonicalFreshKey_fresh)
    (Native.Batch.Slots.slotsInput_storage (measurementBits N) ref 16)

/-- Lifting an earlier pair preserves its structural product through
the sixteen sample cells and factor cell. -/
theorem fixedInput_product {left right : CShape}
    (first : CInputRef (sourceContext base N) left)
    (second : CInputRef (sourceContext base N) right) :
    fixedInput base N (.product first second) =
      .product (fixedInput base N first) (fixedInput base N second) :=
  congrArg
    (fun read : CInputRef
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16)
        (.product left right) =>
      read.underRetained
        (Native.Batch.Slots.samples (sourceContext base N) (measurementBits N) 16).canonicalFreshKey
        (.option (.unsignedWord (modulusBits N)))
        (Native.Batch.Slots.samples (sourceContext base N)
          (measurementBits N) 16).canonicalFreshKey_fresh)
    (Native.Batch.Slots.slotsInput_product (measurementBits N) first second 16)

/-- Bank preparation and measurement cells preserve an earlier structural pair. -/
theorem lifted_product {left right : CShape}
    (first : CInputRef (storageContext base N) left)
    (second : CInputRef (storageContext base N) right) :
    Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N
      (.product first second) =
      .product
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N first)
        (Native.liftInput (storageContext base N) (storage_empty base noQuantum N) N second) := by
  exact congrArg
    (fun read : CInputRef
        (Native.cellsContext (storageContext base N) (storage_empty base noQuantum N) N)
        (.product left right) =>
      read.underRetained
        (Native.cellsContext (storageContext base N)
          (storage_empty base noQuantum N) N).canonicalFreshKey
        (.bits (measurementBits N))
        (Native.cellsContext (storageContext base N)
          (storage_empty base noQuantum N) N).canonicalFreshKey_fresh)
    (MeasurementCells.liftInput_product 2
      (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N first)
      (Native.bankInput (storageContext base N) (storage_empty base noQuantum N) N second)
      (measurementBits N))

private theorem liftWrite_key {shape : CShape}
    (ref : CWriteRef (sourceContext base N) shape) :
    (Native.Batch.Slots.liftWrite N ref).key = ref.key := by
  have same := (congrArg CInputRef.storageKeys (fixedInput_storage base N ref)).symm.trans
    (fixedInput_keys base N (.storage ref.toCStorageRef))
  exact List.singleton_inj.mp same

/-- A caller read avoids the source residue cell that the next batch redraws. -/
theorem caller_source_separated {shape : CShape}
    (observed : CInputRef base shape) :
    (sourceRef base noQuantum N).key ∉
      (callerInput base noQuantum N observed).storageKeys := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  have finalKeys : (callerInput base noQuantum N observed).storageKeys =
      sourceInput.storageKeys :=
    (nativeInput_keys (storage_empty base noQuantum N) N
      (fixedInput base N sourceInput)).trans (fixedInput_keys base N sourceInput)
  let prior := observed.underRetained base.canonicalFreshKey (.bits (residueSamplingBits N))
    base.canonicalFreshKey_fresh
  have retainedKeys : sourceInput.storageKeys = prior.storageKeys :=
    CInputRef.storageKeys_underRetained _ _ _ _
  have oldAbsent : (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).key ∉
      sourceInput.storageKeys :=
    (congrArg (fun keys => base.canonicalFreshKey ∉ keys) retainedKeys).mpr
      (CInputRef.fresh_not_mem_storageKeys_underRetained observed base.canonicalFreshKey
        (.bits (residueSamplingBits N)) base.canonicalFreshKey_fresh)
  have keyEqual := (underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))).trans
        (liftWrite_key base N (ShorStyle.Canonical.Sampler.Retained.sampleRef base N))
  exact (congrArg₂ (fun key keys => key ∉ keys) keyEqual finalKeys).mpr oldAbsent

/-- A caller read avoids the complete parameter cell that the next batch rewrites. -/
theorem caller_parameter_separated {shape : CShape}
    (observed : CInputRef base shape) :
    (parameterRef base noQuantum N).key ∉
      (callerInput base noQuantum N observed).storageKeys := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  have finalKeys : (callerInput base noQuantum N observed).storageKeys =
      sourceInput.storageKeys :=
    (nativeInput_keys (storage_empty base noQuantum N) N
      (fixedInput base N sourceInput)).trans (fixedInput_keys base N sourceInput)
  have oldAbsent : (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).key ∉
      sourceInput.storageKeys :=
    CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _
  have keyEqual := (underBank_key base noQuantum N
    (Native.Batch.Slots.liftWrite N
      (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))).trans
        (liftWrite_key base N (ShorStyle.Canonical.Sampler.Retained.parameterRef base N))
  exact (congrArg₂ (fun key keys => key ∉ keys) keyEqual finalKeys).mpr oldAbsent

/-- The actual factor destination is fresh relative to every original caller read. -/
theorem caller_factor_separated {shape : CShape}
    (observed : CInputRef base shape) :
    (factorRef base noQuantum N).key ∉ (callerInput base noQuantum N observed).storageKeys := by
  let sourceInput := ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) observed
  have finalKeys := nativeInput_keys (storage_empty base noQuantum N) N
    (fixedInput base N sourceInput)
  have oldAbsent :
      (Native.Batch.Slots.factorRef (sourceContext base N) N).key ∉
        (fixedInput base N sourceInput).storageKeys :=
    CInputRef.fresh_not_mem_storageKeys_underRetained _ _ _ _
  exact (congrArg₂ (fun key keys => key ∉ keys)
    (underBank_key base noQuantum N
      (Native.Batch.Slots.factorRef (sourceContext base N) N)) finalKeys).mpr oldAbsent

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
