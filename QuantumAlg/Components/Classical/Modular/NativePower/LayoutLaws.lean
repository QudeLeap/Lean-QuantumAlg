/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.BodyExecution
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Actual identities and reads of lexical modular-power storage

Global key uniqueness separates all three newly allocated cells from one
another and from every original structural input. These proofs account for
the actual contexts and never require a caller-supplied layout certificate.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The complete scratch scope contains exactly its three heads followed by all original keys. -/
theorem nativePower_scope_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (powerCtx ctx width).keys =
      [(accumulatorCell ctx width).key, (baseCell ctx width).key,
        (modulusCell ctx width).key] ++ ctx.keys := rfl

private theorem internal_keys_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    [(accumulatorCell ctx width).key, (baseCell ctx width).key,
      (modulusCell ctx width).key].Nodup := by
  have unique := (powerCtx ctx width).keysNodup
  change (powerCtx ctx width).keys.Nodup at unique
  rw [nativePower_scope_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- All internally generated keys are disjoint from the entire original context. -/
theorem nativePower_scope_keys_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint [(accumulatorCell ctx width).key, (baseCell ctx width).key,
      (modulusCell ctx width).key] ctx.keys := by
  have unique := (powerCtx ctx width).keysNodup
  change (powerCtx ctx width).keys.Nodup at unique
  rw [nativePower_scope_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- Scratch cells are pairwise different in the directions used by actual read/write proofs. -/
theorem nativePower_scope_separation (ctx : RuntimeCtx kind) (width : Nat) :
    (modulusCell ctx width).key ≠ (baseCell ctx width).key ∧
      (accumulatorCell ctx width).key ≠ (modulusCell ctx width).key ∧
      (accumulatorCell ctx width).key ≠ (baseCell ctx width).key := by
  have unique := internal_keys_nodup ctx width
  have accumulatorAbsent := (List.nodup_cons.mp unique).1
  have baseAbsent := (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
  have baseModulus : (baseCell ctx width).key ≠ (modulusCell ctx width).key :=
    fun same => baseAbsent (List.mem_singleton.mpr same)
  refine ⟨Ne.symm baseModulus, ?_, ?_⟩
  · intro same
    exact accumulatorAbsent (List.mem_cons_of_mem _ (List.mem_singleton.mpr same))
  · intro same
    exact accumulatorAbsent (List.mem_cons.mpr (Or.inl same))

/-- Original structural read support remains unchanged through all actual scratch lifts. -/
theorem nativePower_underPower_keys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underPower input width).storageKeys = input.storageKeys := by
  simp only [underPower, CInputRef.storageKeys_underWorkspace]

/-- Every internal write is automatically separate from every original structural input. -/
theorem nativePower_input_separation {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (modulusCell ctx width).key ∉ (underPower input width).storageKeys ∧
      (baseCell ctx width).key ∉ (underPower input width).storageKeys ∧
      (accumulatorCell ctx width).key ∉ (underPower input width).storageKeys := by
  rw [nativePower_underPower_keys]
  have separated := List.disjoint_left.mp (nativePower_scope_keys_disjoint ctx width)
  have absent (key : StorageKey)
      (internal : key ∈ [(accumulatorCell ctx width).key, (baseCell ctx width).key,
        (modulusCell ctx width).key]) : key ∉ input.storageKeys :=
    fun present => separated internal (input.storageKeys_subset_context present)
  exact ⟨absent _ (by simp), absent _ (by simp), absent _ (by simp)⟩

/-- Every original value is read unchanged after the three actual scratch allocations. -/
theorem nativePower_enterPower_read {shape : CShape} (store : Store ctx)
    (input : CInputRef ctx shape) (width : Nat) :
    (enterPower store width).read (underPower input width) = store.read input := by
  simp only [enterPower, underPower, Store.read_pushWorkspace_underWorkspace]

/-- Reading the final outer store is the same read under the exact scratch heads being popped. -/
theorem nativePower_leavePower_read {shape : CShape}
    (store : Store (powerCtx ctx width)) (input : CInputRef ctx shape) :
    (leavePower store).read input = store.read (underPower input width) := by
  simp only [leavePower, underPower, Store.read_popWorkspace_underWorkspace]

/-- The allocated accumulator contains the actual canonical zero encoding. -/
theorem nativePower_enterPower_accumulator (store : Store ctx) (width : Nat) :
    (enterPower store width).read (wordRead (accumulatorCell ctx width)) =
      CShape.wordOfNat width 0 := rfl

/-- Reading the lifted destination agrees with lifting its original structural read. -/
theorem nativePower_writeUnderPower_read {shape : CShape}
    (output : CWriteRef ctx shape) (width : Nat) :
    wordRead (writeUnderPower output width) = underPower (wordRead output) width := rfl

/-- The complete scope preserves all quantum physical identities and dimensions. -/
theorem nativePower_scope_quantumWires (ctx : RuntimeCtx kind) (width : Nat) :
    (powerCtx ctx width).quantumWires = ctx.quantumWires := rfl

end QuantumAlg.ClassicalRoutines.Modular.NativePower
