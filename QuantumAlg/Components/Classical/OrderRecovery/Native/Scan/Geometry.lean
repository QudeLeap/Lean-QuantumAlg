/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Frame
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization.Frame

/-!
# Structural separation of the actual recovery scan cells

The fixed recovery allocation proves the placement obligations of the
arithmetic and branch lemmas. These facts follow from actual fresh keys,
including under the lexical division pair; they are not input promises of
the recovery algorithm.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

/-- The actual writable scan cells are distinct and cannot overwrite the constant reads. -/
structure ScanCells.Separated (cells : ScanCells ctx modulusWidth candidateWidth) : Prop where
  /-- Each real persistent destination has its own storage key. -/
  distinct : cells.writeKeys.Nodup
  /-- The stored zero word survives every persistent scan write. -/
  zeroFree : ∀ key ∈ cells.writeKeys, key ∉ cells.zero.storageKeys
  /-- The stored modular one survives every persistent scan write. -/
  oneFree : ∀ key ∈ cells.writeKeys, key ∉ cells.one.storageKeys

/-- Distinct positions in that actual write list have distinct storage identities. -/
lemma nativeScan_separated_keys (cells : ScanCells ctx modulusWidth candidateWidth)
    (separated : cells.Separated) (first second : Fin 11) (different : first ≠ second) :
    cells.writeKeys.get first ≠ cells.writeKeys.get second := by
  intro same
  exact different ((List.nodup_iff_injective_get.mp separated.distinct) same)

/-- A structural lift through the actual division head preserves all placement facts. -/
lemma nativeScan_separated_underWorkspace (cells : ScanCells ctx modulusWidth candidateWidth)
    (separated : cells.Separated) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (cells.underWorkspace key shape fresh).Separated := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nativeScan_writeKeys_underWorkspace]
    exact separated.distinct
  · intro written member
    rw [nativeScan_writeKeys_underWorkspace] at member
    change written ∉ (cells.zero.underWorkspace key shape fresh).storageKeys
    rw [CInputRef.storageKeys_underWorkspace]
    exact separated.zeroFree written member
  · intro written member
    rw [nativeScan_writeKeys_underWorkspace] at member
    change written ∉ (cells.one.underWorkspace key shape fresh).storageKeys
    rw [CInputRef.storageKeys_underWorkspace]
    exact separated.oneFree written member

/-- The genuine recovery fields discharge every persistent scan-placement obligation. -/
lemma nativeRecovery_scan_separated (modulusWidth candidateWidth : Nat) :
    (recoveryCells ctx modulusWidth candidateWidth).Separated := by
  have positions : ([4, 5, 2, 3, 6, 8, 7, 9, 12, 10, 11] :
      List (Fin recoveryFields.length)).Nodup := by decide
  have realKeys : (recoveryCells ctx modulusWidth candidateWidth).writeKeys =
      ([4, 5, 2, 3, 6, 8, 7, 9, 12, 10, 11] : List (Fin recoveryFields.length)).map
        (fun index => (recoveryFieldCell ctx modulusWidth candidateWidth
          recoveryFields index).key) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [realKeys]
    exact positions.map (nativeRecovery_field_injective modulusWidth candidateWidth recoveryFields)
  · intro key member
    rw [realKeys] at member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    apply nativeRecovery_field_read_separate modulusWidth candidateWidth index 0
    intro same
    subst index
    exact (by decide : (0 : Fin recoveryFields.length) ∉
      ([4, 5, 2, 3, 6, 8, 7, 9, 12, 10, 11] : List (Fin recoveryFields.length))) present
  · intro key member
    rw [realKeys] at member
    obtain ⟨index, present, rfl⟩ := List.mem_map.mp member
    apply nativeRecovery_field_read_separate modulusWidth candidateWidth index 1
    intro same
    subst index
    exact (by decide : (1 : Fin recoveryFields.length) ∉
      ([4, 5, 2, 3, 6, 8, 7, 9, 12, 10, 11] : List (Fin recoveryFields.length))) present

/-- Every original source read is separate from all actual recovery scan destinations. -/
lemma nativeRecovery_scan_input_separate (modulusWidth candidateWidth : Nat)
    {shape : CShape} (input : CInputRef ctx shape) :
    ∀ key ∈ (recoveryCells ctx modulusWidth candidateWidth).writeKeys,
      key ∉ (underRecoveryFields modulusWidth candidateWidth recoveryFields input).storageKeys := by
  intro key member
  change key ∈
    ([4, 5, 2, 3, 6, 8, 7, 9, 12, 10, 11] : List (Fin recoveryFields.length)).map
      (fun index => (recoveryFieldCell ctx modulusWidth candidateWidth
        recoveryFields index).key) at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact nativeRecovery_field_input_separate modulusWidth candidateWidth recoveryFields index input

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
