/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Parity

/-!
# Runtime parity values and preservation of the actual input cells

Only the two supplied writable bits change. Both operands of every actual
AND are read from the incoming Store because the program preserves all
table and measured-mask inputs throughout its chronological fold.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeParity

open Execution

noncomputable section

variable {ctx : RuntimeCtx .quantum}

private lemma andOp_read (temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) (store : Store ctx) :
    ((store.applyOp (andOp temporary input)).read (.storage temporary.toCStorageRef)).toBool =
      ((store.read input.1).toBool && (store.read input.2).toBool) := by
  have written := Store.read_applyOp_output store (andOp temporary input)
  change (store.applyOp (andOp temporary input)).read (.storage temporary.toCStorageRef) = _
    at written
  rw [written]
  change (Resource.BitOpcode.eval .and
    (.product (store.read input.1) (store.read input.2))).toBool = _
  cases first : store.read input.1
  cases second : store.read input.2
  rfl

private lemma xorOp_read (parity : CWriteRef ctx .bit) (input : CInputRef ctx .bit)
    (store : Store ctx) :
    ((store.applyOp (MaskParity.xorOp parity input)).read (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^ (store.read input).toBool) := by
  have written := Store.read_applyOp_output store (MaskParity.xorOp parity input)
  change (store.applyOp (MaskParity.xorOp parity input)).read (.storage parity.toCStorageRef) = _
    at written
  rw [written]
  change (Resource.BitOpcode.eval .xor
    (.product (store.read (.storage parity.toCStorageRef)) (store.read input))).toBool = _
  cases first : store.read (.storage parity.toCStorageRef)
  cases second : store.read input
  rfl

/-- A complete pair changes only its two real output cells. -/
lemma stepStore_read_other (parity temporary : CWriteRef ctx .bit)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) {shape : CShape}
    (observed : CInputRef ctx shape) (freeParity : parity.key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (stepStore parity temporary input store).read observed = store.read observed := by
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (MaskParity.xorOp parity (.storage temporary.toCStorageRef)) observed freeParity).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (andOp temporary input) observed
        freeTemporary)

private lemma value_congr (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (before after : Store ctx)
    (agree : ∀ input ∈ pairs, after.read input.1 = before.read input.1 ∧
      after.read input.2 = before.read input.2) : value pairs after = value pairs before := by
  induction pairs with
  | nil => rfl
  | cons input rest ih =>
      change (((after.read input.1).toBool && (after.read input.2).toBool) ^^
        value rest after) = _
      rw [(agree input (by simp)).1, (agree input (by simp)).2,
        ih (fun other member => agree other (by simp [member]))]
      rfl

/-- The actual pair XORs precisely its original two-input AND into the accumulator. -/
lemma stepStore_parity (parity temporary : CWriteRef ctx .bit)
    (different : parity.key ≠ temporary.key)
    (input : CInputRef ctx .bit × CInputRef ctx .bit) (store : Store ctx) :
    ((stepStore parity temporary input store).read (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^
        ((store.read input.1).toBool && (store.read input.2).toBool)) := by
  unfold stepStore
  rw [xorOp_read, andOp_read]
  rw [Store.read_applyOp_of_not_mem_storageKeys store (andOp temporary input)
    (.storage parity.toCStorageRef)
    (by
      change temporary.key ∉ [parity.key]
      simpa only [List.mem_singleton] using Ne.symm different)]

/-- All other caller cells, including every table row and every measured bit, remain unchanged. -/
lemma foldStore_read_other (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) {shape : CShape}
    (observed : CInputRef ctx shape) (freeParity : parity.key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (foldStore parity temporary pairs store).read observed = store.read observed := by
  induction pairs generalizing store with
  | nil => rfl
  | cons input rest ih =>
      rw [foldStore, ih]
      exact stepStore_read_other parity temporary input observed freeParity freeTemporary store

/-- Every contribution uses its original Store values; the incoming accumulator remains explicit. -/
lemma foldStore_parity (parity temporary : CWriteRef ctx .bit)
    (different : parity.key ≠ temporary.key)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (freeParity : ∀ input ∈ pairs,
      parity.key ∉ input.1.storageKeys ∧ parity.key ∉ input.2.storageKeys)
    (freeTemporary : ∀ input ∈ pairs,
      temporary.key ∉ input.1.storageKeys ∧ temporary.key ∉ input.2.storageKeys)
    (store : Store ctx) :
    ((foldStore parity temporary pairs store).read (.storage parity.toCStorageRef)).toBool =
      ((store.read (.storage parity.toCStorageRef)).toBool ^^ value pairs store) := by
  induction pairs generalizing store with
  | nil => simp only [foldStore, value, List.foldr_nil, Bool.xor_false]
  | cons input rest ih =>
      rw [foldStore, ih
        (fun other member => freeParity other (by simp [member]))
        (fun other member => freeTemporary other (by simp [member])),
        stepStore_parity parity temporary different]
      have retained : value rest (stepStore parity temporary input store) = value rest store := by
        apply value_congr
        intro other member
        exact ⟨stepStore_read_other parity temporary input other.1
            (freeParity other (by simp [member])).1
            (freeTemporary other (by simp [member])).1 store,
          stepStore_read_other parity temporary input other.2
            (freeParity other (by simp [member])).2
            (freeTemporary other (by simp [member])).2 store⟩
      rw [retained]
      exact Bool.xor_assoc _ _ _

/-- The real cleared output contains exactly the original runtime table/mask dot product. -/
lemma storeStep_parity (parity temporary : CWriteRef ctx .bit)
    (different : parity.key ≠ temporary.key)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit))
    (freeParity : ∀ input ∈ pairs,
      parity.key ∉ input.1.storageKeys ∧ parity.key ∉ input.2.storageKeys)
    (freeTemporary : ∀ input ∈ pairs,
      temporary.key ∉ input.1.storageKeys ∧ temporary.key ∉ input.2.storageKeys)
    (store : Store ctx) :
    ((storeStep parity temporary pairs store).read (.storage parity.toCStorageRef)).toBool =
      value pairs store := by
  rw [storeStep, foldStore_parity parity temporary different pairs freeParity freeTemporary,
    MaskParity.clearOp_read, Bool.false_xor]
  apply value_congr
  intro input member
  exact ⟨Store.read_applyOp_of_not_mem_storageKeys store (MaskParity.clearOp parity)
      input.1 (freeParity input member).1,
    Store.read_applyOp_of_not_mem_storageKeys store (MaskParity.clearOp parity)
      input.2 (freeParity input member).2⟩

/-- Clearing and all real AND/XOR pairs preserve the rest of the complete caller Store. -/
lemma storeStep_read_other (parity temporary : CWriteRef ctx .bit)
    (pairs : List (CInputRef ctx .bit × CInputRef ctx .bit)) {shape : CShape}
    (observed : CInputRef ctx shape) (freeParity : parity.key ∉ observed.storageKeys)
    (freeTemporary : temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (storeStep parity temporary pairs store).read observed = store.read observed := by
  rw [storeStep, foldStore_read_other parity temporary pairs observed freeParity freeTemporary]
  exact Store.read_applyOp_of_not_mem_storageKeys store (MaskParity.clearOp parity)
    observed freeParity

end

end QuantumAlg.EncodedBit.WindowLookup.RuntimeParity
