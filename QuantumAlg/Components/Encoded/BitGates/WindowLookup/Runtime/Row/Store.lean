/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Correctness
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity.Character

/-!
# Original runtime table values in the actual parity row

Every original table word and measured bit remains unchanged throughout the
paid row. The reusable temporary bit is distinct from all column outputs.
Consequently each final parity cell contains its own original table/mask
character, despite the complete chronological sequence of actual overwrites.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeRow

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- The same original table words, observed only for mathematical execution statements. -/
def readTable (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (store : Store ctx) (index : Fin columns) : Fin (2 ^ wordWidth) :=
  ⟨(store.read (table index)).toNat, (store.read (table index)).toNat_lt⟩

/-- Every row stage preserves all caller inputs outside its actual writable cells. -/
lemma rowRecord_read_other (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth)) (indices : List (Fin columns))
    {shape : CShape} (observed : CInputRef ctx shape)
    (freeParity : ∀ index ∈ indices, (parity index).key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    ((rowRecord (oracles := oracles) (services := services)
      measured parity temporary table indices store).1).read observed = store.read observed := by
  induction indices generalizing store with
  | nil => rfl
  | cons index rest ih =>
      change ((rowRecord (oracles := oracles) (services := services)
        measured parity temporary table rest
        (RuntimeParity.record (oracles := oracles) (services := services) (parity index) temporary
          (RuntimeParity.inputs (table index) measured) store).1).1).read observed = _
      rw [ih (fun other member => freeParity other (by simp [member])), RuntimeParity.record_store]
      exact RuntimeParity.storeStep_read_other (parity index) temporary _ observed
        (freeParity index (by simp)) freeTemporary store

private lemma inputs_free (measured : CInputRef ctx (.bits wordWidth))
    (table : CInputRef ctx (.unsignedWord wordWidth)) (key : StorageKey)
    (tableFree : key ∉ table.storageKeys) (maskFree : key ∉ measured.storageKeys) :
    ∀ input ∈ RuntimeParity.inputs table measured,
      key ∉ input.1.storageKeys ∧ key ∉ input.2.storageKeys := by
  intro input member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact ⟨tableFree, maskFree⟩

private lemma inputs_value_congr (measured : CInputRef ctx (.bits wordWidth))
    (table : CInputRef ctx (.unsignedWord wordWidth)) (before after : Store ctx)
    (sameTable : after.read table = before.read table)
    (sameMask : after.read measured = before.read measured) :
    RuntimeParity.value (RuntimeParity.inputs table measured) after =
      RuntimeParity.value (RuntimeParity.inputs table measured) before := by
  rw [RuntimeParity.value_inputs, RuntimeParity.value_inputs, sameTable, sameMask]

/-- Every actual column contains the character of its original stored word and measured mask. -/
lemma rowRecord_read_parity (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (distinct : Function.Injective (fun index => (parity index).key))
    (temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key)
    (maskFree : ∀ index, (parity index).key ∉ measured.storageKeys)
    (temporaryMaskFree : temporary.key ∉ measured.storageKeys)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (tableFree : ∀ index column, (parity index).key ∉ (table column).storageKeys)
    (temporaryTableFree : ∀ column, temporary.key ∉ (table column).storageKeys)
    (indices : List (Fin columns)) (unique : indices.Nodup)
    (label : Fin columns) (present : label ∈ indices) (store : Store ctx) :
    (((rowRecord (oracles := oracles) (services := services)
      measured parity temporary table indices store).1).read
        (.storage (parity label).toCStorageRef)).toBool =
      RuntimeParity.value (RuntimeParity.inputs (table label) measured) store := by
  induction indices generalizing store with
  | nil => simp at present
  | cons index rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      change (((rowRecord (oracles := oracles) (services := services)
        measured parity temporary table rest
        (RuntimeParity.record (oracles := oracles) (services := services) (parity index) temporary
          (RuntimeParity.inputs (table index) measured) store).1).1).read
            (.storage (parity label).toCStorageRef)).toBool = _
      by_cases selected : index = label
      · subst index
        rw [rowRecord_read_other measured parity temporary table rest
          (.storage (parity label).toCStorageRef)
          (by
            intro other member
            change (parity other).key ∉ [(parity label).key]
            intro same
            exact absent ((distinct (List.mem_singleton.mp same)) ▸ member))
          (by
            change temporary.key ∉ [(parity label).key]
            simpa only [List.mem_singleton] using Ne.symm (temporaryDifferent label)),
          RuntimeParity.record_store]
        exact RuntimeParity.storeStep_parity (parity label) temporary (temporaryDifferent label) _
          (inputs_free measured (table label) _ (tableFree label label) (maskFree label))
          (inputs_free measured (table label) _ (temporaryTableFree label) temporaryMaskFree) store
      · have tailPresent : label ∈ rest :=
          (List.mem_cons.mp present).resolve_left (Ne.symm selected)
        rw [ih tailUnique tailPresent, RuntimeParity.record_store]
        apply inputs_value_congr
        · exact RuntimeParity.storeStep_read_other (parity index) temporary _ (table label)
            (tableFree index label) (temporaryTableFree label) store
        · exact RuntimeParity.storeStep_read_other (parity index) temporary _ measured
            (maskFree index) temporaryMaskFree store

/-- The physical branch reads exactly the row constant computed from the same original Store. -/
lemma storedRowConstant_eq (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (distinct : Function.Injective (fun index => (parity index).key))
    (temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key)
    (maskFree : ∀ index, (parity index).key ∉ measured.storageKeys)
    (temporaryMaskFree : temporary.key ∉ measured.storageKeys)
    (table : Fin columns → CInputRef ctx (.unsignedWord wordWidth))
    (tableFree : ∀ index column, (parity index).key ∉ (table column).storageKeys)
    (temporaryTableFree : ∀ column, temporary.key ∉ (table column).storageKeys)
    (store : Store ctx) :
    MaskParity.storedConstant ((rowRecord (oracles := oracles) (services := services)
      measured parity temporary table (List.ofFn fun index : Fin columns => index) store).1.read
        (MaskParity.rowInput parity)) =
      MaskParity.rowConstant (readTable table store) (store.read measured) := by
  unfold MaskParity.storedConstant MaskParity.rowConstant
  apply Fin.ext
  apply congrArg (fun bits : Fin columns → Bool => Nat.ofBits bits)
  funext index
  change (((rowRecord (oracles := oracles) (services := services)
    measured parity temporary table (List.ofFn fun index : Fin columns => index) store).1).read
      (.storage (parity index).toCStorageRef)).toBool = _
  rw [rowRecord_read_parity measured parity temporary distinct temporaryDifferent maskFree
    temporaryMaskFree table tableFree temporaryTableFree _
    (List.nodup_ofFn_ofInjective (fun _ _ same => same)) index
    (List.mem_ofFn.mpr ⟨index, rfl⟩), RuntimeParity.value_inputs]
  rfl

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeRow
