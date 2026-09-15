/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor
import Mathlib.Data.List.Nodup

/-!
# Exact stored-word semantics of Euclidean cursor advancement

Distinct actual cursor cells and the fresh division pair justify every read
across the preceding writes. The result therefore rotates the original words
and tests the original remainder, with no free arithmetic performed by a read.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual copy exposes precisely the value read from its source store. -/
theorem nativeCursor_copy_read (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (copyCursorWord input output)).read (cellRead output) = store.read input :=
  Store.read_applyOp_output store (copyCursorWord input output)

private theorem copy_read_other {shape : CShape}
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (other : CWriteRef ctx shape)
    (different : output.key ≠ other.key) (store : Store ctx) :
    (store.applyOp (copyCursorWord input output)).read (cellRead other) =
      store.read (cellRead other) :=
  Store.read_applyOp_of_not_mem_storageKeys store (copyCursorWord input output) (cellRead other)
    (fun present => different (List.mem_singleton.mp present))

private theorem copy_read_external {shape : CShape}
    (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (store.applyOp (copyCursorWord input output)).read other = store.read other :=
  Store.read_applyOp_of_not_mem_storageKeys store (copyCursorWord input output) other separate

private theorem active_read_other {shape : CShape} (cells : CursorCells ctx width)
    (zero : CInputRef ctx (.unsignedWord width)) (other : CWriteRef ctx shape)
    (different : cells.active.key ≠ other.key) (store : Store ctx) :
    (store.applyOp (cursorActiveOp cells zero)).read (cellRead other) =
      store.read (cellRead other) :=
  Store.read_applyOp_of_not_mem_storageKeys store (cursorActiveOp cells zero) (cellRead other)
    (fun present => different (List.mem_singleton.mp present))

private theorem active_read (cells : CursorCells ctx width)
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    (store.applyOp (cursorActiveOp cells zero)).read (cellRead cells.active) =
      .bit (decide ((store.read zero).toNat <
        (store.read (cellRead cells.denominator)).toNat)) :=
  Store.read_applyOp_output store (cursorActiveOp cells zero)

/-- The actual five writes rotate the exact original words and read the same remainder. -/
theorem nativeCursor_advance_reads (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width))
    (distinct : [cells.older.key, cells.previous.key, cells.numerator.key,
      cells.denominator.key, cells.candidate.key, cells.active.key].Nodup)
    (remainderFree : ∀ key ∈ [cells.older.key, cells.previous.key, cells.numerator.key],
      key ∉ remainder.storageKeys)
    (zeroFree : ∀ key ∈ [cells.older.key, cells.previous.key, cells.numerator.key,
      cells.denominator.key], key ∉ zero.storageKeys) (store : Store ctx) :
    (advanceCursorStore cells remainder zero store).read (cellRead cells.older) =
        store.read (cellRead cells.previous) ∧
      (advanceCursorStore cells remainder zero store).read (cellRead cells.previous) =
        store.read (cellRead cells.candidate) ∧
      (advanceCursorStore cells remainder zero store).read (cellRead cells.numerator) =
        store.read (cellRead cells.denominator) ∧
      (advanceCursorStore cells remainder zero store).read (cellRead cells.denominator) =
        store.read remainder ∧
      (advanceCursorStore cells remainder zero store).read (cellRead cells.active) =
        .bit (decide ((store.read zero).toNat < (store.read remainder).toNat)) := by
  let keys := [cells.older.key, cells.previous.key, cells.numerator.key,
    cells.denominator.key, cells.candidate.key, cells.active.key]
  have different (first second : Fin 6) (notSame : first ≠ second) :
      keys.get first ≠ keys.get second :=
    fun same => notSame ((List.nodup_iff_injective_get.mp distinct) same)
  have olderRemainder := remainderFree cells.older.key (by simp)
  have previousRemainder := remainderFree cells.previous.key (by simp)
  have numeratorRemainder := remainderFree cells.numerator.key (by simp)
  have olderZero := zeroFree cells.older.key (by simp)
  have previousZero := zeroFree cells.previous.key (by simp)
  have numeratorZero := zeroFree cells.numerator.key (by simp)
  have denominatorZero := zeroFree cells.denominator.key (by simp)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold advanceCursorStore
    rw [active_read_other _ _ _ (different 5 0 (by decide)),
      copy_read_other _ _ _ (different 3 0 (by decide)),
      copy_read_other _ _ _ (different 2 0 (by decide)),
      copy_read_other _ _ _ (different 1 0 (by decide)), nativeCursor_copy_read]
  · unfold advanceCursorStore
    rw [active_read_other _ _ _ (different 5 1 (by decide)),
      copy_read_other _ _ _ (different 3 1 (by decide)),
      copy_read_other _ _ _ (different 2 1 (by decide)), nativeCursor_copy_read,
      copy_read_other _ _ _ (different 0 4 (by decide))]
  · unfold advanceCursorStore
    rw [active_read_other _ _ _ (different 5 2 (by decide)),
      copy_read_other _ _ _ (different 3 2 (by decide)), nativeCursor_copy_read,
      copy_read_other _ _ _ (different 1 3 (by decide)),
      copy_read_other _ _ _ (different 0 3 (by decide))]
  · unfold advanceCursorStore
    rw [active_read_other _ _ _ (different 5 3 (by decide)), nativeCursor_copy_read,
      copy_read_external _ _ _ numeratorRemainder,
      copy_read_external _ _ _ previousRemainder,
      copy_read_external _ _ _ olderRemainder]
  · unfold advanceCursorStore
    rw [active_read, copy_read_external _ _ _ denominatorZero,
      copy_read_external _ _ _ numeratorZero, copy_read_external _ _ _ previousZero,
      copy_read_external _ _ _ olderZero, nativeCursor_copy_read,
      copy_read_external _ _ _ numeratorRemainder,
      copy_read_external _ _ _ previousRemainder,
      copy_read_external _ _ _ olderRemainder]

/-- All other real structural reads survive an actual rejected-candidate update. -/
theorem nativeCursor_advance_read_other (cells : CursorCells ctx width)
    (remainder zero : CInputRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape)
    (separate : ∀ key ∈ [cells.older.key, cells.previous.key, cells.numerator.key,
      cells.denominator.key, cells.active.key], key ∉ other.storageKeys) (store : Store ctx) :
    (advanceCursorStore cells remainder zero store).read other = store.read other := by
  unfold advanceCursorStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (cursorActiveOp cells zero) other
    (separate cells.active.key (by simp)), copy_read_external _ _ _ (separate _ (by simp)),
    copy_read_external _ _ _ (separate _ (by simp)),
    copy_read_external _ _ _ (separate _ (by simp)),
    copy_read_external _ _ _ (separate _ (by simp))]

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
