/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.StateLayout
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Storage facts derived from the actual Euclidean lexical layout

Every nonaliasing fact follows from the real context's globally distinct keys.
The store maps below are precisely the pushes and pops already performed by
the three existing workspace instructions. Their read equations transport the
input and final result across those scopes without a new caller assumption.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Lifting an existing operand beneath the loop state preserves its exact stored-key support. -/
theorem gcdLayout_underLoop_keys {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    (underLoop input width).storageKeys = input.storageKeys := by
  let first : CInputRef (currentCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let second : CInputRef (previousCtx ctx width) shape := first.underWorkspace
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh
  exact (CInputRef.storageKeys_underWorkspace second
    (previousCtx ctx width).canonicalFreshKey .bit
    (previousCtx ctx width).canonicalFreshKey_fresh).trans
    ((CInputRef.storageKeys_underWorkspace first (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).trans
      (CInputRef.storageKeys_underWorkspace input ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh))

/-- Actual lexical state cells are distinct in the directions used by the update equations. -/
theorem gcdLayout_state_separation (ctx : RuntimeCtx kind) (width : Nat) :
    (currentCell ctx width).key ≠ (previousCell ctx width).key ∧
      (conditionCell ctx width).key ≠ (currentCell ctx width).key ∧
      (conditionCell ctx width).key ≠ (previousCell ctx width).key := by
  have unique := gcdState_keys_nodup ctx width
  have conditionAbsent := (List.nodup_cons.mp unique).1
  have previousAbsent := (List.nodup_cons.mp (List.nodup_cons.mp unique).2).1
  have previousCurrent : (previousCell ctx width).key ≠ (currentCell ctx width).key :=
    fun same => previousAbsent (List.mem_singleton.mpr same)
  refine ⟨Ne.symm previousCurrent, ?_, ?_⟩
  · intro same
    exact conditionAbsent (List.mem_cons_of_mem _ (List.mem_singleton.mpr same))
  · intro same
    exact conditionAbsent (List.mem_cons.mpr (Or.inl same))

/-- No internally generated state key occurs in any structurally read original operand. -/
theorem gcdLayout_input_separation {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) :
    (currentCell ctx width).key ∉ (underLoop input width).storageKeys ∧
      (previousCell ctx width).key ∉ (underLoop input width).storageKeys ∧
      (conditionCell ctx width).key ∉ (underLoop input width).storageKeys := by
  rw [gcdLayout_underLoop_keys]
  have separated := List.disjoint_left.mp (gcdState_keys_disjoint ctx width)
  have absent (key : StorageKey)
      (internal : key ∈ [(conditionCell ctx width).key, (previousCell ctx width).key,
        (currentCell ctx width).key]) : key ∉ input.storageKeys :=
    fun present => separated internal (input.storageKeys_subset_context present)
  exact ⟨absent _ (by simp), absent _ (by simp), absent _ (by simp)⟩

/-- Actual successive store extensions on entry to the three lexical state scopes. -/
def pushLoopStore (width : Nat) (store : Store ctx) : Store (loopCtx ctx width) :=
  ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh).pushWorkspace
        (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh

/-- Actual reverse store releases on exit from those same three lexical scopes. -/
def popLoopStore (width : Nat) (store : Store (loopCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
      (currentCtx ctx width).canonicalFreshKey_fresh
      (Store.popWorkspace (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh store))

/-- Entering all three scopes preserves every original structural read exactly. -/
theorem gcdLayout_push_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store ctx) :
    (pushLoopStore width store).read (underLoop input width) = store.read input := by
  let first : CInputRef (currentCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let second : CInputRef (previousCtx ctx width) shape := first.underWorkspace
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh
  let firstStore : Store (currentCtx ctx width) :=
    store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let secondStore : Store (previousCtx ctx width) := firstStore.pushWorkspace
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh
  exact (Store.read_pushWorkspace_underWorkspace secondStore
    (previousCtx ctx width).canonicalFreshKey .bit
    (previousCtx ctx width).canonicalFreshKey_fresh second).trans
    ((Store.read_pushWorkspace_underWorkspace firstStore (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh first).trans
      (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord width) ctx.canonicalFreshKey_fresh input))

/-- Leaving all three scopes exposes each final original-cell value unchanged. -/
theorem gcdLayout_pop_read {shape : CShape} (input : CInputRef ctx shape)
    (width : Nat) (store : Store (loopCtx ctx width)) :
    (popLoopStore width store).read input = store.read (underLoop input width) := by
  let first : CInputRef (currentCtx ctx width) shape :=
    input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
  let second : CInputRef (previousCtx ctx width) shape := first.underWorkspace
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh
  let secondStore : Store (previousCtx ctx width) := Store.popWorkspace
    (previousCtx ctx width).canonicalFreshKey .bit
    (previousCtx ctx width).canonicalFreshKey_fresh store
  let firstStore : Store (currentCtx ctx width) := Store.popWorkspace
    (currentCtx ctx width).canonicalFreshKey (.unsignedWord width)
    (currentCtx ctx width).canonicalFreshKey_fresh secondStore
  exact (Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord width) ctx.canonicalFreshKey_fresh firstStore input).trans
    ((Store.read_popWorkspace_underWorkspace (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh secondStore first).trans
      (Store.read_popWorkspace_underWorkspace (previousCtx ctx width).canonicalFreshKey .bit
        (previousCtx ctx width).canonicalFreshKey_fresh store second))

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
