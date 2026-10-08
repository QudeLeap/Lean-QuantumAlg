/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Construction
import all QuantumAlg.Components.Classical.NumberTheory.GCD.RemainderSemantics
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact Euclidean update through its real division scope

The temporary quotient/remainder pair is allocated by the existing workspace
instruction. Its fresh identity is derived from the actual context, so it
cannot alias either Euclidean word, the branch bit or an existing input.
Popping this cell preserves all older reads and the complete quantum-reference
blocks. Its initial contents are never assumed to encode a caller-supplied value.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The concrete store and real five-instruction path after the lexical division scope. -/
def scopedRemainderStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx × (scopedRemainder (model := model) first second zero
      active).Path :=
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let final := remainderStep (model := model)
    (first.underWorkspace key (operandShape width) fresh)
    (second.underWorkspace key (operandShape width) fresh)
    (zero.underWorkspace key (operandShape width) fresh)
    (active.underWorkspace key (operandShape width) fresh)
    (CWriteRef.workspaceHead ctx key (operandShape width) fresh)
    (store.pushWorkspace key (operandShape width) fresh)
  (Store.popWorkspace key (operandShape width) fresh final.1, final.2)

/-- Actual lexical execution is the exact allocated-store update with its real body path. -/
theorem gcdScopedRemainder_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scopedRemainder (model := model) first second zero active).execute Reference state =
      state.mapClassical (fun entry =>
        let result := scopedRemainderStep (model := model) first second zero active entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let first' := first.underWorkspace key (operandShape width) fresh
  let second' := second.underWorkspace key (operandShape width) fresh
  let zero' := zero.underWorkspace key (operandShape width) fresh
  let active' := active.underWorkspace key (operandShape width) fresh
  let scratch := CWriteRef.workspaceHead ctx key (operandShape width) fresh
  refine (Circuit.execute_workspace_mapClassical key (operandShape width) fresh
    (remainderBody (model := model) first' second' zero' active' scratch)
    (fun before =>
      let result := remainderStep (model := model) first' second' zero' active' scratch before.1
      ((result.1, before.2), result.2))
    (fun reference {_} _ initial => by
      exact (gcdRemainder_execute (model := model)
        first' second' zero' active' scratch reference initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)) Reference state).trans
            (ExecutionState.executionState_mapClassical_congr _ rfl)


private theorem liftedWrite_key {shape workspaceShape : CShape} (output : CWriteRef ctx shape)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (output.underWorkspace key workspaceShape fresh).key = output.key := rfl

private theorem fresh_ne_cell {shape : CShape} (output : CWriteRef ctx shape) :
    ctx.canonicalFreshKey ≠ output.key := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  rw [same]
  exact List.mem_map_of_mem output.toCStorageRef.present

/-- Every original structural read outside the three persistent written cells is unchanged. -/
theorem gcdScopedRemainder_read_other {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    {observed : CShape} (other : CInputRef ctx observed)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (store : Store ctx) :
    ((scopedRemainderStep (model := model) first second zero active store).1).read other =
      store.read other := by
  unfold scopedRemainderStep
  change (Store.popWorkspace _ _ _ (remainderStore _ _ _ _ _ _)).read other = _
  rw [Store.read_popWorkspace_underWorkspace]
  rw [gcdRemainder_read_other]
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other
  · simpa only [CInputRef.storageKeys_underWorkspace, liftedWrite_key] using firstFree
  · simpa only [CInputRef.storageKeys_underWorkspace, liftedWrite_key] using secondFree
  · simpa only [CInputRef.storageKeys_underWorkspace, liftedWrite_key] using activeFree
  · rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh
      (other.storageKeys_subset_context present)

/-- The scoped update implements exact total division and rotation on its persistent cells. -/
theorem gcdScopedRemainder_store_values {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (store : Store ctx) :
    let final := (scopedRemainderStep (model := model) first second zero active store).1
    (final.read (cellRead first)).toNat =
        (store.read (cellRead second)).toNat % (store.read (cellRead first)).toNat ∧
      final.read (cellRead second) = store.read (cellRead first) ∧
      (final.read (cellRead active)).toBool =
        decide ((store.read (cellRead second)).toNat %
          (store.read (cellRead first)).toNat ≠ (store.read zero).toNat) ∧
      final.read zero = store.read zero := by
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let first' := first.underWorkspace key (operandShape width) fresh
  let second' := second.underWorkspace key (operandShape width) fresh
  let zero' := zero.underWorkspace key (operandShape width) fresh
  let active' := active.underWorkspace key (operandShape width) fresh
  let scratch := CWriteRef.workspaceHead ctx key (operandShape width) fresh
  have firstZero' : first'.key ∉ zero'.storageKeys := by
    simpa only [first', zero', CInputRef.storageKeys_underWorkspace, liftedWrite_key]
      using firstZero
  have secondZero' : second'.key ∉ zero'.storageKeys := by
    simpa only [second', zero', CInputRef.storageKeys_underWorkspace, liftedWrite_key]
      using secondZero
  have activeZero' : active'.key ∉ zero'.storageKeys := by
    simpa only [active', zero', CInputRef.storageKeys_underWorkspace, liftedWrite_key]
      using activeZero
  have scratchZero' : scratch.key ∉ zero'.storageKeys := by
    rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => fresh (zero.storageKeys_subset_context present)
  have actual := gcdRemainder_store_values first' second' zero' active' scratch
    firstSecond (fresh_ne_cell first) (Ne.symm (fresh_ne_cell second)) activeFirst activeSecond
    firstZero' secondZero' activeZero' scratchZero'
    (store.pushWorkspace key (operandShape width) fresh)
  have liftRead {shape : CShape} (output : CWriteRef ctx shape) :
      cellRead (output.underWorkspace key (operandShape width) fresh) =
        (cellRead output).underWorkspace key (operandShape width) fresh := rfl
  simpa only [scopedRemainderStep, remainderStep, BitWord.instructionStep, remainderStore,
    Store.read_popWorkspace_underWorkspace,
    first', second', zero', active', scratch, liftRead,
    Store.read_pushWorkspace_underWorkspace] using actual

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
