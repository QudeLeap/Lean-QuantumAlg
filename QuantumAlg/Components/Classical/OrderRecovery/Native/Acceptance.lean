/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor.Laws

/-!
# Actual acceptance-latch readback

The same candidate and validation values read by the acceptance branch are
written to its selected-word and accepted-bit cells. Negating the actual true
validation clears activity, so later finite slots cannot overwrite the first
accepted result.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem bit_copy_read (input : CInputRef ctx .bit) (output : CWriteRef ctx .bit)
    (store : Store ctx) :
    (store.applyOp (.bit .copy ctx input output)).read (cellRead output) = store.read input :=
  Store.read_applyOp_output store (.bit .copy ctx input output)

private theorem bit_not_read (input : CInputRef ctx .bit) (output : CWriteRef ctx .bit)
    (store : Store ctx) :
    (store.applyOp (.bit .not ctx input output)).read (cellRead output) =
      .bit (!(store.read input).toBool) := by
  refine (Store.read_applyOp_output store (.bit .not ctx input output)).trans ?_
  change Resource.BitOpcode.eval .not (store.read input) = _
  cases store.read input
  rfl

/-- Acceptance stores the original candidate, copies validity and negates it into activity. -/
theorem nativeCursor_accept_reads (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit)
    (activeSelected : active.key ≠ selected.key)
    (activeAccepted : active.key ≠ accepted.key)
    (acceptedSelected : accepted.key ≠ selected.key)
    (selectedValid : selected.key ∉ valid.storageKeys)
    (acceptedValid : accepted.key ∉ valid.storageKeys) (store : Store ctx) :
    (acceptCursorStore candidate valid selected accepted active store).read (cellRead selected) =
        store.read candidate ∧
      (acceptCursorStore candidate valid selected accepted active store).read (cellRead accepted) =
        store.read valid ∧
      (acceptCursorStore candidate valid selected accepted active store).read (cellRead active) =
        .bit (!(store.read valid).toBool) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold acceptCursorStore
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (.bit .not ctx valid active)
      (cellRead selected) (fun present => activeSelected (List.mem_singleton.mp present)),
      Store.read_applyOp_of_not_mem_storageKeys _ (.bit .copy ctx valid accepted)
        (cellRead selected) (fun present => acceptedSelected (List.mem_singleton.mp present)),
      nativeCursor_copy_read]
  · unfold acceptCursorStore
    rw [Store.read_applyOp_of_not_mem_storageKeys _ (.bit .not ctx valid active)
      (cellRead accepted) (fun present => activeAccepted (List.mem_singleton.mp present)),
      bit_copy_read,
      Store.read_applyOp_of_not_mem_storageKeys store (copyCursorWord candidate selected)
        valid selectedValid]
  · unfold acceptCursorStore
    rw [bit_not_read,
      Store.read_applyOp_of_not_mem_storageKeys _ (.bit .copy ctx valid accepted)
        valid acceptedValid,
      Store.read_applyOp_of_not_mem_storageKeys store (copyCursorWord candidate selected)
        valid selectedValid]

/-- Acceptance changes only its selected word and two writable latches. -/
theorem nativeCursor_accept_read_other (candidate : CInputRef ctx (.unsignedWord width))
    (valid : CInputRef ctx .bit) (selected : CWriteRef ctx (.unsignedWord width))
    (accepted active : CWriteRef ctx .bit) {shape : CShape} (other : CInputRef ctx shape)
    (selectedFree : selected.key ∉ other.storageKeys)
    (acceptedFree : accepted.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (store : Store ctx) :
    (acceptCursorStore candidate valid selected accepted active store).read other =
      store.read other := by
  unfold acceptCursorStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (.bit .not ctx valid active) other activeFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (.bit .copy ctx valid accepted) other acceptedFree,
    Store.read_applyOp_of_not_mem_storageKeys store (copyCursorWord candidate selected)
      other selectedFree]

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
