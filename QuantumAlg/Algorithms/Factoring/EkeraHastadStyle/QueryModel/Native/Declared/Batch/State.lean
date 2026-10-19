/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Program
import all QuantumAlg.Core.Execution.Measurement.Cells.Frame
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual writes of the selected declared EH batch

Every copied sample is written to its dedicated retained slot. The store
equations below expose the physical reads and preserve earlier slots, so the
joint probability proof can reason about the chronological batch history.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma sampleKeys {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width count : Nat) :
    Function.Injective (fun index =>
      (Native.Batch.Slots.sampleRef ctx width count index).key) := by
  induction count with
  | zero => intro index; exact Fin.elim0 index
  | succ count ih =>
      intro left right same
      revert same
      refine Fin.cases ?_ (fun left => ?_) left
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro _; rfl
        · intro same
          change (Native.Batch.Slots.samples ctx width count).canonicalFreshKey =
            (Native.Batch.Slots.sampleRef ctx width count right).key at same
          have present := MeasurementCells.reference_key_mem
            (Native.Batch.Slots.sampleRef ctx width count right).toCStorageRef
          exact False.elim ((Native.Batch.Slots.samples ctx width count).canonicalFreshKey_fresh
            (same.symm ▸ present))
      · refine Fin.cases ?_ (fun right => ?_) right
        · intro same
          change (Native.Batch.Slots.sampleRef ctx width count left).key =
            (Native.Batch.Slots.samples ctx width count).canonicalFreshKey at same
          have present := MeasurementCells.reference_key_mem
            (Native.Batch.Slots.sampleRef ctx width count left).toCStorageRef
          exact False.elim ((Native.Batch.Slots.samples ctx width count).canonicalFreshKey_fresh
            (same ▸ present))
        · intro same
          exact congrArg Fin.succ (ih same)

attribute [local irreducible] Native.Batch.Slots.samples

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat)

variable {environment : (model N).Environment}

/-- Structural placement beneath the bank preserves the sample-slot key. -/
lemma underBank_key {shape : CShape}
    (ref : CWriteRef (storageContext base N) shape) :
    (underBank base noQuantum N ref).key = ref.key := by
  unfold underBank
  exact MeasurementCells.liftWrite_key 2 _ (measurementBits N)

/-- All sixteen actual terminal sample cells have different keys. -/
lemma terminal_keys :
    Function.Injective (fun index => (terminalRef base noQuantum N index).key) := by
  intro left right same
  have oldKeys := (underBank_key base noQuantum N
    (Native.Batch.Slots.terminalRef (sourceContext base N) N left)).symm.trans
      (same.trans (underBank_key base noQuantum N
        (Native.Batch.Slots.terminalRef (sourceContext base N) N right)))
  change (Native.Batch.Slots.sampleRef (sourceContext base N)
    (measurementBits N) 16 left).key =
      (Native.Batch.Slots.sampleRef (sourceContext base N)
        (measurementBits N) 16 right).key at oldKeys
  exact sampleKeys (sourceContext base N) (measurementBits N) 16 oldKeys

/-- The copied value comes from actual finite measurement cells. -/
def copiedValue (store : Store (context base noQuantum N)) :
    (CShape.bits (measurementBits N)).Value :=
  CShape.packFiniteBits (measurementBits N)
    (store.read (.fixedVector fun position =>
      .storage (Native.cells (storageContext base N)
        (storage_empty base noQuantum N) N position).toCStorageRef))

/-- The paid bit pack overwrites one persistent sample cell. -/
def copyStep (index : Fin 16) (store : Store (context base noQuantum N)) :
    Store (context base noQuantum N) × (copy base noQuantum N index).Path :=
  BitWord.instructionStep (execution := model N)
    (copyOp base noQuantum N index) store

/-- The complete copy execution preserves all quantum-reference blocks. -/
lemma copy_execute (index : Fin 16) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History)) :
    (copy base noQuantum N index).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((copyStep base noQuantum N index entry.1).1,
          (entry.2.1, (entry.2.2,
            (copyStep base noQuantum N index entry.1).2)))) := by
  exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model N)
    (copyOp base noQuantum N index) state

/-- Reading the destination after the pack returns the actual measured bits. -/
lemma copy_read (index : Fin 16)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N index store).1.read
      (.storage (terminalRef base noQuantum N index).toCStorageRef) =
        copiedValue base noQuantum N store :=
  Store.read_applyOp_output store (copyOp base noQuantum N index)

/-- The copy leaves every other sample slot unchanged. -/
lemma copy_other (written observed : Fin 16) (different : written ≠ observed)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N written store).1.read
      (.storage (terminalRef base noQuantum N observed).toCStorageRef) =
        store.read (.storage (terminalRef base noQuantum N observed).toCStorageRef) :=
  Store.read_write_other store _ _ _
    (fun same => different (terminal_keys base noQuantum N same))

/-- Any structural read outside the destination cell is preserved. -/
lemma copy_frame {shape : CShape} (written : Fin 16)
    (observed : CInputRef (context base noQuantum N) shape)
    (separate : (terminalRef base noQuantum N written).key ∉ observed.storageKeys)
    (store : Store (context base noQuantum N)) :
    (copyStep base noQuantum N written store).1.read observed =
      store.read observed :=
  Store.read_applyOp_of_not_mem_storageKeys store
    (copyOp base noQuantum N written) observed separate

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
