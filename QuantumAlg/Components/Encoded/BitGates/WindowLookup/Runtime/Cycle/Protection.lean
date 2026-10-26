/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Cycle.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Runtime.Row.Protection
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Stored-array wiring supplies runtime table preservation

The actual builder array is one existing closed-shape storage cell. Finite
measurement cells, bit masks and individual parity bits have different
shapes, so none can alias it in the same sealed runtime context. Only
distinctness of the same-shaped writable parity work bits remains explicit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.RuntimeTable

open Execution

variable {ctx : RuntimeCtx .quantum} {wordWidth lowWidth highRemaining : Nat}

private lemma differentShape_key_ne {firstShape secondShape : CShape}
    (first : CWriteRef ctx firstShape) (second : CWriteRef ctx secondShape)
    (different : firstShape ≠ secondShape) : first.key ≠ second.key := by
  intro same
  exact different
    (CStorageRef.storageRef_shape_eq_of_key first.toCStorageRef second.toCStorageRef same)

/-- Every original high/low word reads exactly the actual builder array's storage key. -/
lemma splitInputs_stored_storageKeys
    (array : CWriteRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (top : Bool) (high : Fin (2 ^ highRemaining)) (low : Fin (2 ^ lowWidth)) :
    (splitInputs (.storage array.toCStorageRef) top high low).storageKeys = [array.key] := rfl

/-- Actual stored arrays are protected from all paid parity work and retain the measured mask. -/
lemma splitInputs_stored_protection
    (array : CWriteRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (mask : CWriteRef ctx (.bits wordWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit) (temporary : CWriteRef ctx .bit)
    (parityDistinct : Function.Injective fun index => (parity index).key)
    (temporaryDifferent : ∀ index, (parity index).key ≠ temporary.key) :
    RuntimeRow.Protection (.storage mask.toCStorageRef) parity temporary
      (fun row : Bool × Fin (2 ^ highRemaining) =>
        splitInputs (.storage array.toCStorageRef) row.1 row.2) := by
  constructor
  · exact parityDistinct
  · exact temporaryDifferent
  · intro index
    change (parity index).key ∉ [mask.key]
    simpa only [List.mem_singleton] using
      differentShape_key_ne (parity index) mask (by intro same; cases same)
  · change temporary.key ∉ [mask.key]
    simpa only [List.mem_singleton] using
      differentShape_key_ne temporary mask (by intro same; cases same)
  · intro index row column
    rw [splitInputs_stored_storageKeys]
    simpa only [List.mem_singleton] using
      differentShape_key_ne (parity index) array (by intro same; cases same)
  · intro row column
    rw [splitInputs_stored_storageKeys]
    simpa only [List.mem_singleton] using
      differentShape_key_ne temporary array (by intro same; cases same)

/-- The actual MZ finite output cells cannot alias any of the stored builder-array reads. -/
lemma splitInputs_stored_output_free
    (array : CWriteRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (output : Fin wordWidth → CWriteRef ctx (.finite 2))
    (index : Fin wordWidth) (top : Bool) (high : Fin (2 ^ highRemaining))
    (low : Fin (2 ^ lowWidth)) :
    (output index).key ∉
      (splitInputs (.storage array.toCStorageRef) top high low).storageKeys := by
  rw [splitInputs_stored_storageKeys]
  simpa only [List.mem_singleton] using
    differentShape_key_ne (output index) array (by intro same; cases same)

/-- The paid measured-mask pack writes a different actual cell from the complete builder array. -/
lemma splitInputs_stored_mask_free
    (array : CWriteRef ctx
      (.fixedVector (2 ^ (highRemaining + lowWidth + 1)) (.unsignedWord wordWidth)))
    (mask : CWriteRef ctx (.bits wordWidth)) (top : Bool) (high : Fin (2 ^ highRemaining))
    (low : Fin (2 ^ lowWidth)) :
    mask.key ∉ (splitInputs (.storage array.toCStorageRef) top high low).storageKeys := by
  rw [splitInputs_stored_storageKeys]
  simpa only [List.mem_singleton] using
    differentShape_key_ne mask array (by intro same; cases same)

end QuantumAlg.EncodedBit.WindowLookup.RuntimeTable
