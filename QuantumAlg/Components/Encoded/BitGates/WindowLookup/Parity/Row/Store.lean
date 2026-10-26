/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Row

/-!
# Exact original-input values in the actual row parity cells

The finite chronological record writes only the supplied parity cells.
Distinct cell keys preserve previously computed columns and the original
measured mask. Every final parity is therefore the XOR of the original
measured positions selected by that column's static table word.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.MaskParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {wordWidth columns : Nat}

/-- Every structural read outside the actually written column cells is retained. -/
lemma rowRecord_read_other (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (table : Fin columns → Fin (2 ^ wordWidth)) (indices : List (Fin columns))
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ index ∈ indices, (parity index).key ∉ observed.storageKeys) (store : Store ctx) :
    ((rowRecord (oracles := oracles) (services := services)
      measured parity table indices store).1).read observed = store.read observed := by
  induction indices generalizing store with
  | nil => rfl
  | cons index rest ih =>
      change ((rowRecord (oracles := oracles) (services := services) measured parity table rest
        (record (oracles := oracles) (services := services) (parity index)
          (selectedInputs measured (table index)) store).1).1).read observed = _
      rw [ih (fun other member => separate other (by simp [member])), record_store]
      exact storeStep_read_other (parity index) _ observed (separate index (by simp)) store

private lemma selectedInputs_separate (measured : CInputRef ctx (.bits wordWidth))
    (constant : Fin (2 ^ wordWidth)) (parity : CWriteRef ctx .bit)
    (separate : parity.key ∉ measured.storageKeys) :
    ∀ input ∈ selectedInputs measured constant, parity.key ∉ input.storageKeys := by
  intro input member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact separate

private lemma selectedInputs_value_congr (measured : CInputRef ctx (.bits wordWidth))
    (constant : Fin (2 ^ wordWidth)) (first second : Store ctx)
    (same : first.read measured = second.read measured) :
    value (selectedInputs measured constant) first =
      value (selectedInputs measured constant) second := by
  unfold selectedInputs
  generalize Word.constantOneIndices constant = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      have bitRead : first.read (.bitsGet measured index) = second.read (.bitsGet measured index) :=
        congrArg (fun bits => bits.bitGet index) same
      change ((first.read (.bitsGet measured index)).toBool ^^
        value (rest.map fun position => CInputRef.bitsGet measured position) first) = _
      rw [bitRead, ih]
      rfl

/-- Each actual final parity cell contains its table column's original measured-mask parity. -/
lemma rowRecord_read_parity (measured : CInputRef ctx (.bits wordWidth))
    (parity : Fin columns → CWriteRef ctx .bit)
    (distinct : Function.Injective (fun index => (parity index).key))
    (separate : ∀ index, (parity index).key ∉ measured.storageKeys)
    (table : Fin columns → Fin (2 ^ wordWidth)) (indices : List (Fin columns))
    (unique : indices.Nodup) (label : Fin columns) (present : label ∈ indices) (store : Store ctx) :
    (((rowRecord (oracles := oracles) (services := services)
      measured parity table indices store).1).read (.storage (parity label).toCStorageRef)).toBool =
        value (selectedInputs measured (table label)) store := by
  induction indices generalizing store with
  | nil => simp at present
  | cons index rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      change (((rowRecord (oracles := oracles) (services := services) measured parity table rest
        (record (oracles := oracles) (services := services) (parity index)
          (selectedInputs measured (table index)) store).1).1).read
            (.storage (parity label).toCStorageRef)).toBool = _
      by_cases selected : index = label
      · subst index
        rw [rowRecord_read_other measured parity table rest (.storage (parity label).toCStorageRef)
          (by
            intro other member
            change (parity other).key ∉ [(parity label).key]
            intro same
            exact absent ((distinct (List.mem_singleton.mp same)) ▸ member)), record_store]
        exact storeStep_read (parity label) _
          (selectedInputs_separate measured _ _ (separate label)) store
      · have tailPresent : label ∈ rest :=
          (List.mem_cons.mp present).resolve_left (Ne.symm selected)
        rw [ih tailUnique tailPresent, record_store]
        apply selectedInputs_value_congr
        exact storeStep_read_other (parity index) _ measured (separate index) store

end

end QuantumAlg.EncodedBit.WindowLookup.MaskParity
