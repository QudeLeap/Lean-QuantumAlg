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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Allocate the product temporary around the actual multiply/add program. -/
def scopedContinuant (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  .workspace ctx key (.unsignedWord width) fresh
    (continuantBody
      (quotient.underWorkspace key (.unsignedWord width) fresh)
      (previous.underWorkspace key (.unsignedWord width) fresh)
      (older.underWorkspace key (.unsignedWord width) fresh)
      (CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh)
      (candidate.underWorkspace key (.unsignedWord width) fresh))

/-- The resulting outer store and the path of its two actual operations. -/
def scopedContinuantStep (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (scopedContinuant quotient previous older candidate).Path :=
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let final := continuantStore
    (quotient.underWorkspace key (.unsignedWord width) fresh)
    (previous.underWorkspace key (.unsignedWord width) fresh)
    (older.underWorkspace key (.unsignedWord width) fresh)
    (CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh)
    (candidate.underWorkspace key (.unsignedWord width) fresh)
    (store.pushWorkspace key (.unsignedWord width) fresh)
  (Store.popWorkspace key (.unsignedWord width) fresh final, ((), ()))

/-- The lexical program has this exact action on every complete quantum-reference block. -/
theorem nativeScopedContinuant_execute
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scopedContinuant quotient previous older candidate).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopedContinuantStep quotient previous older candidate entry.1).1,
          (entry.2, (scopedContinuantStep quotient previous older candidate entry.1).2))) := by
  let key := ctx.canonicalFreshKey
  let fresh := ctx.canonicalFreshKey_fresh
  let quotient' := quotient.underWorkspace key (.unsignedWord width) fresh
  let previous' := previous.underWorkspace key (.unsignedWord width) fresh
  let older' := older.underWorkspace key (.unsignedWord width) fresh
  let candidate' := candidate.underWorkspace key (.unsignedWord width) fresh
  let product := CWriteRef.workspaceHead ctx key (.unsignedWord width) fresh
  refine (Circuit.execute_workspace_mapClassical key (.unsignedWord width) fresh
    (continuantBody quotient' previous' older' product candidate')
    (fun store => (continuantStore quotient' previous' older' product candidate' store,
      ((), ())))
    (fun reference {_} _ initial => by
      refine (nativeContinuant_execute quotient' previous' older' product candidate'
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1

private theorem liftedWrite_key {shape workspaceShape : CShape} (output : CWriteRef ctx shape)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (output.underWorkspace key workspaceShape fresh).key = output.key := rfl

/-- The output realizes the recurrence on the original reads, without a temporary alias premise. -/
theorem nativeScopedContinuant_result
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((scopedContinuantStep quotient previous older candidate store).1).read
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
  simpa only [scopedContinuantStep, Store.read_popWorkspace_underWorkspace,
    quotient', previous', older', candidate', product, liftRead,
    Store.read_pushWorkspace_underWorkspace] using actual

/-- Only the declared candidate cell can change among all pre-existing structural reads. -/
theorem nativeScopedContinuant_read_other
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) (store : Store ctx) :
    ((scopedContinuantStep quotient previous older candidate store).1).read other =
      store.read other := by
  unfold scopedContinuantStep
  rw [Store.read_popWorkspace_underWorkspace]
  rw [nativeContinuant_read_other]
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other
  · rw [CInputRef.storageKeys_underWorkspace]
    exact fun present => ctx.canonicalFreshKey_fresh
      (other.storageKeys_subset_context present)
  · simpa only [CInputRef.storageKeys_underWorkspace, liftedWrite_key] using separate

/-- Allocation and exact release introduce no extra arithmetic event. -/
theorem nativeScopedContinuant_eventTrace
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (scopedContinuant quotient previous older candidate).Path) :
    (scopedContinuant quotient previous older candidate).eventTrace path =
      continuantEvents kind width := rfl

/-- The multiplication and dependent addition retain their exact sequential depth. -/
theorem nativeScopedContinuant_unitDepth
    (quotient previous older : CInputRef ctx (.unsignedWord width))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (scopedContinuant quotient previous older candidate).Path) :
    (scopedContinuant quotient previous older candidate).depth (fun _ => 1) path = 2 := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
