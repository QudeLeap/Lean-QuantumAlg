/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Continuant
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Continuant update with one actual lexical product cell

The quotient and both previous denominators are read from existing storage.
A fresh product word is allocated, written, read by the addition, and then
popped by the same workspace instruction. Freshness follows from the actual
context; callers do not supply a separation assumption for this temporary.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Allocate the product temporary around the actual multiply/add program. -/
def scopedContinuant (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  .workspace ctx key (.unsignedWord width) fresh
    (continuantBody (model := model)
      (quotient.underWorkspace key (.unsignedWord width) fresh)
      (previous.underWorkspace key (.unsignedWord width) fresh)
      (older.underWorkspace key (.unsignedWord width) fresh)
      (CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh)
      (candidate.underWorkspace key (.unsignedWord width) fresh))

/-- The resulting outer store and the path of its two actual operations. -/
def scopedContinuantStep (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (scopedContinuant (model := model) quotient previous older candidate).Path :=
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let final := continuantStep (model := model)
    (quotient.underWorkspace key (.unsignedWord width) fresh)
    (previous.underWorkspace key (.unsignedWord width) fresh)
    (older.underWorkspace key (.unsignedWord width) fresh)
    (CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh)
    (candidate.underWorkspace key (.unsignedWord width) fresh)
    (store.pushWorkspace key (.unsignedWord width) fresh)
  (Store.popWorkspace key (.unsignedWord width) fresh final.1, final.2)

/-- The lexical program has this exact action on every complete quantum-reference block. -/
lemma nativeScopedContinuant_execute
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (scopedContinuant (model := model) quotient previous older candidate).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        ((scopedContinuantStep (model := model) quotient previous older candidate entry.1).1,
          (entry.2.1, (entry.2.2,
            (scopedContinuantStep (model := model) quotient previous older candidate
              entry.1).2)))) := by
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let quotient' := quotient.underWorkspace key (.unsignedWord width) fresh
  let previous' := previous.underWorkspace key (.unsignedWord width) fresh
  let older' := older.underWorkspace key (.unsignedWord width) fresh
  let candidate' := candidate.underWorkspace key (.unsignedWord width) fresh
  let product := CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) key (.unsignedWord width) fresh
    (continuantBody (model := model) quotient' previous' older' product candidate')
    (fun entry =>
      let next := continuantStep (model := model) quotient' previous' older' product candidate'
        entry.1
      ((next.1, entry.2), next.2))
    (fun reference {_} _ initial => by
      refine (nativeContinuant_execute quotient' previous' older' product candidate'
        reference initial).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma liftedWrite_key {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape workspaceShape : CShape} (output : CWriteRef ctx shape)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (output.underWorkspace key workspaceShape fresh).key = output.key := rfl

/-- The output realizes the recurrence on the original reads, without a temporary alias premise. -/
lemma nativeScopedContinuant_result
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((scopedContinuantStep (model := model) quotient previous older candidate store).1).read
        (cellRead candidate) =
      continuantValue (store.read quotient) (store.read previous) (store.read older) := by
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let quotient' := quotient.underWorkspace key (.unsignedWord width) fresh
  let previous' := previous.underWorkspace key (.unsignedWord width) fresh
  let older' := older.underWorkspace key (.unsignedWord width) fresh
  let candidate' := candidate.underWorkspace key (.unsignedWord width) fresh
  let product := CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh
  have separate : product.key ∉ older'.storageKeys := by
    rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => fresh (older.storageKeys_subset_context present)
  have actual := nativeContinuant_result quotient' previous' older' product candidate'
    separate (store.pushWorkspace key (.unsignedWord width) fresh)
  have liftRead : cellRead candidate' =
      (cellRead candidate).underWorkspace key (.unsignedWord width) fresh := rfl
  simpa only [scopedContinuantStep, continuantStep, BitWord.instructionStep, continuantStore,
    Store.read_popWorkspace_underWorkspace,
    quotient', previous', older', candidate', product, liftRead,
    Store.read_pushWorkspace_underWorkspace] using actual

/-- Only the declared candidate cell can change among all pre-existing structural reads. -/
lemma nativeScopedContinuant_read_other
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) (store : Store ctx) :
    ((scopedContinuantStep (model := model) quotient previous older candidate store).1).read other =
      store.read other := by
  unfold scopedContinuantStep
  change (Store.popWorkspace _ _ _ (continuantStore _ _ _ _ _ _)).read other = _
  rw [Store.read_popWorkspace_underWorkspace]
  rw [nativeContinuant_read_other]
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other
  · rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh
      (other.storageKeys_subset_context present)
  · simpa only [CInputRef.storageKeys_underWorkspace, liftedWrite_key] using separate

/-- Allocation and exact release introduce no extra arithmetic event. -/
lemma nativeScopedContinuant_eventTrace
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (scopedContinuant (model := model) quotient previous older candidate).Path) :
    (scopedContinuant (model := model) quotient previous older candidate).eventTrace path =
      continuantEvents model width := by
  apply nativeContinuant_eventTrace

/-- The multiplication and dependent addition retain their exact sequential depth. -/
lemma nativeScopedContinuant_unitDepth
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (scopedContinuant (model := model) quotient previous older candidate).Path) :
    (scopedContinuant (model := model) quotient previous older candidate).depth
      (fun _ => 1) path = 2 := by
  apply nativeContinuant_unitDepth

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
