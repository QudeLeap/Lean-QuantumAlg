/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Entry
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Values

/-!
# Original persistent reads survive actual local recovery

Candidate arithmetic writes its four fresh words. Both complete checks write
only their real checker cells and the reused candidate remainder word. The
local selection writes its four fresh local latches. Consequently every
original structural read, including earlier persistent acceptance and its
full factor word, survives all these instructions before narrowing begins.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original inputs retain their actual positions beneath all thirteen local cells. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (context ctx width) shape :=
  CheckLayout.underRead (arithmeticRead input width) (RSA.quadraticWordWidth width)

/-- The complete lift retains precisely the original source-key support. -/
theorem nativeQuadratic_persistent_underRead_keys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys :=
  (CheckLayout.nativeQuadratic_checkLayout_underRead_keys (arithmeticRead input width)
    (RSA.quadraticWordWidth width)).trans
    ((nativeQuadratic_underRead_keys
      (SelectionLayout.underRead input (RSA.quadraticWordWidth width))).trans
      (SelectionLayout.nativeRecovery_selection_underRead_keys input
        (RSA.quadraticWordWidth width)))

private theorem selection_underWrite_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    CInputRef.storage (selectionUnderWrite output width).toCStorageRef =
      SelectionLayout.underRead (.storage output.toCStorageRef)
        (RSA.quadraticWordWidth width) := rfl

set_option maxHeartbeats 800000 in -- Align read references across thirteen actual scope cells.
/-- A lifted writable cell reads exactly the same original storage under the complete layout. -/
theorem nativeQuadratic_persistent_underWrite_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    CInputRef.storage (underWrite output width).toCStorageRef =
      underRead (.storage output.toCStorageRef) width := by
  have arithmetic := (Layout.nativeQuadratic_layout_underWrite_read
    (selectionUnderWrite output width) width).trans
    (congrArg (fun input : CInputRef (selectionContext ctx width) shape =>
      Layout.underRead input width) (selection_underWrite_read output width))
  exact (CheckLayout.nativeQuadratic_checkLayout_underWrite_read
    (Layout.underWrite (selectionUnderWrite output width) width)
    (RSA.quadraticWordWidth width)).trans
    (congrArg (fun input : CInputRef (candidateContext ctx width) shape =>
      CheckLayout.underRead input (RSA.quadraticWordWidth width)) arithmetic)

/-- No actual local selector destination belongs to any original structural source. -/
theorem nativeQuadratic_persistent_local_key_free {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (index : Fin 4) :
    SelectionLayout.cellKey ctx (RSA.quadraticWordWidth width) index ∉
      (underRead input width).storageKeys := by
  have support : (underRead input width).storageKeys =
      (SelectionLayout.underRead input (RSA.quadraticWordWidth width)).storageKeys :=
    (CheckLayout.nativeQuadratic_checkLayout_underRead_keys (arithmeticRead input width)
      (RSA.quadraticWordWidth width)).trans
      (nativeQuadratic_underRead_keys
        (SelectionLayout.underRead input (RSA.quadraticWordWidth width)))
  exact fun present => SelectionLayout.original_free input
    (RSA.quadraticWordWidth width) index (support ▸ present)

/-- The actual initialized arithmetic preserves each original persistent source value. -/
theorem nativeQuadratic_persistent_initialized_read
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    {shape : CShape} (other : CInputRef ctx shape) (store : Store ctx) :
    (initializedStore input modulus store).read (arithmeticRead other width) =
      store.read other :=
  (nativeQuadratic_initialized_read_other (arithmeticRead input width)
    (arithmeticRead modulus width) (arithmeticRefs ctx width) (arithmeticRead other width)
    (writes_free (SelectionLayout.underRead other (RSA.quadraticWordWidth width)) width)
    (entryStore width store)).trans (nativeQuadratic_local_entry_read other width store)

private theorem pair_preserves_read {current : RuntimeCtx kind} {pairWidth : Nat}
    (refs : Pair.Refs current pairWidth) {shape : CShape} (other : CInputRef current shape)
    (availableFree : refs.selection.available.key ∉ other.storageKeys)
    (takeFree : refs.selection.take.key ∉ other.storageKeys)
    (acceptedFree : refs.selection.accepted.key ∉ other.storageKeys)
    (selectedFree : refs.selection.selected.key ∉ other.storageKeys) (store : Store current)
    (checks : (Pair.checkedStore refs store).read other = store.read other) :
    (Pair.step refs store).1.read other = store.read other :=
  (Selection.nativeQuadratic_selection_read_other
    (Pair.selectedInputs refs.first) (Pair.selectedInputs refs.second) refs.selection other
    availableFree takeFree acceptedFree selectedFree (Pair.checkedStore refs store)).trans checks

set_option maxHeartbeats 800000 in -- Match pair inputs beneath eight outer and five check cells.
/-- Both complete checks and both local selectors leave every original read unchanged. -/
theorem nativeQuadratic_persistent_pair_read
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    {shape : CShape} (other : CInputRef ctx shape) (store : Store (context ctx width)) :
    (Pair.step (pairRefs modulus) store).1.read (underRead other width) =
      store.read (underRead other width) := by
  have remainderFree : (operands modulus).remainder.key ∉
      (arithmeticRead other width).storageKeys :=
    nativeQuadratic_underRead_free
      (SelectionLayout.underRead other (RSA.quadraticWordWidth width))
      (arithmeticRefs ctx width).root.key
      (List.get_mem (Layout.internalKeys (selectionContext ctx width) width)
        ⟨2, by change 2 < 4; decide⟩)
  exact pair_preserves_read (pairRefs modulus) (underRead other width)
    (nativeQuadratic_persistent_local_key_free other width 1)
    (nativeQuadratic_persistent_local_key_free other width 0)
    (nativeQuadratic_persistent_local_key_free other width 3)
    (nativeQuadratic_persistent_local_key_free other width 2)
    store (CheckLayout.nativeQuadratic_checks_read_original (operands modulus)
      (arithmeticRead other width) remainderFree store)

/-- Actual entry, arithmetic and local checking preserve the caller's complete stored values. -/
theorem nativeQuadratic_persistent_checked_entry_read
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    {shape : CShape} (other : CInputRef ctx shape) (store : Store ctx) :
    (Pair.step (pairRefs modulus) (CheckLayout.pushStore (RSA.quadraticWordWidth width)
      (initializedStore input modulus store))).1.read (underRead other width) =
      store.read other :=
  (nativeQuadratic_persistent_pair_read modulus other _).trans
    ((CheckLayout.nativeQuadratic_checkLayout_push_read (arithmeticRead other width)
      (RSA.quadraticWordWidth width) (initializedStore input modulus store)).trans
      (nativeQuadratic_persistent_initialized_read input modulus other store))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.LocalLayout
