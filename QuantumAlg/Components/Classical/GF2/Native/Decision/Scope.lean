/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision.Values
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Unique
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Original GF(2) decision values through both real temporary scopes

The actual masked word and equality latch are allocated and popped in their
original order. Their freshness discharges all temporary-cell separation.
The caller's candidate and zero references may alias and hold arbitrary words;
these statements compare their actual original contents.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

omit [BitWord.Selected model] in
private def lifted {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (decisionContext ctx width) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh

omit [BitWord.Selected model] in
private def entered (store : Store ctx) (width : Nat) : Store (decisionContext ctx width) :=
  (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh

omit [BitWord.Selected model] in
private theorem entered_read (store : Store ctx) (width : Nat) {shape : CShape}
    (input : CInputRef ctx shape) : (entered store width).read (lifted input width) =
      store.read input := by
  unfold entered lifted
  rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace]

omit [BitWord.Selected model] in
private theorem exited_read (store : Store (decisionContext ctx width)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
      (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
        (pivotMaskContext ctx width).canonicalFreshKey_fresh store)).read input =
      store.read (lifted input width) := by
  rw [Store.read_popWorkspace_underWorkspace, Store.read_popWorkspace_underWorkspace]
  rfl

omit [BitWord.Selected model] in
private theorem latch_fresh {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    (pivotLatch (pivotMaskContext ctx width)).key ∉ (lifted input width).storageKeys := by
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => (pivotMaskContext ctx width).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

omit [BitWord.Selected model] in
private theorem latch_separate (success : CWriteRef ctx .bit) (width : Nat) :
    (pivotLatch (pivotMaskContext ctx width)).key ≠ (decisionWrite width success).key := by
  have fresh := latch_fresh (.storage success.toCStorageRef) width
  change _ ∉ [success.key] at fresh
  simpa only [List.mem_singleton, decisionWrite, CWriteRef.underWorkspace,
    CStorageRef.underWorkspace] using fresh

/-- The complete original candidate check retains success exactly when the two words differ. -/
theorem gf2CandidateNonzero_success (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    ((checkCandidateNonzeroStep candidate zero success store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        !(decide ((store.read (.storage candidate.toCStorageRef)).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat))) := by
  change ((Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh _)).read _).toBool = _
  rw [exited_read]
  change ((decisionTestStep true (decisionWrite width candidate) (decisionWrite width zero)
    (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))
    (entered store width)).1.read (.storage (decisionWrite width success).toCStorageRef)).toBool = _
  rw [gf2DecisionTest_success _ _ _ _ _ (latch_separate success width)]
  change (((entered store width).read (lifted (.storage success.toCStorageRef) width)).toBool &&
    (decide (((entered store width).read (lifted (.storage candidate.toCStorageRef) width)).toNat =
      ((entered store width).read (lifted (.storage zero.toCStorageRef) width)).toNat) != true)) = _
  rw [entered_read, entered_read, entered_read]
  exact congrArg (fun value => (store.read (.storage success.toCStorageRef)).toBool && value)
    (Bool.bne_true _)

/-- The actual two scopes preserve every caller input outside the original success bit. -/
theorem gf2CandidateNonzero_read_other (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (checkCandidateNonzeroStep candidate zero success store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh _)).read _ = _
  rw [exited_read]
  refine (gf2DecisionTest_read_other true (decisionWrite width candidate) (decisionWrite width zero)
    (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width)) (entered store width)
    (lifted other width) ?_ (latch_fresh other width)).trans (entered_read store width other)
  change success.key ∉ (lifted other width).storageKeys
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact separate

omit [BitWord.Selected model] in
private theorem work_fresh {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    (decisionWork ctx width).key ∉ (lifted input width).storageKeys := by
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

omit [BitWord.Selected model] in
private theorem work_separate {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    (decisionWork ctx width).key ≠ (decisionWrite width output).key := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  change ctx.canonicalFreshKey = output.key at same
  rw [same]
  exact CInputRef.storageKeys_subset_context (.storage output.toCStorageRef)
    (by simp [CInputRef.storageKeys])

omit [BitWord.Selected model] in
private theorem entered_write (store : Store ctx) (width : Nat) {shape : CShape}
    (output : CWriteRef ctx shape) :
    (entered store width).read (.storage (decisionWrite width output).toCStorageRef) =
      store.read (.storage output.toCStorageRef) :=
  entered_read store width (.storage output.toCStorageRef)

/-- The actual scoped uniqueness check compares the original free mask and arbitrary zero source. -/
theorem gf2UniqueFree_success (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) :
    ((selectUniqueFreeStep free zero success store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        decide ((CShape.wordBitAnd width (store.read (.storage free.toCStorageRef))
          (CShape.wordSub width (store.read (.storage free.toCStorageRef))
            (CShape.wordOfNat width 1))).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat) &&
        !decide ((store.read (.storage free.toCStorageRef)).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat)) := by
  change ((Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh _)).read _).toBool = _
  rw [exited_read]
  refine (gf2UniqueFreeBody_success (decisionWrite width free) (decisionWrite width zero)
    (decisionWork ctx width) (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))
    (work_separate free width) (work_separate zero width) (latch_separate success width)
    (entered store width)).trans ?_
  rw [entered_write, entered_write, entered_write]

/-- Both actual uniqueness scopes preserve every caller read outside their success destination. -/
theorem gf2UniqueFree_read_other (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (selectUniqueFreeStep free zero success store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh _)).read _ = _
  rw [exited_read]
  refine (gf2UniqueFreeBody_read_other (decisionWrite width free) (decisionWrite width zero)
    (decisionWork ctx width) (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))
    (entered store width) (lifted other width) (work_fresh other width) ?_
    (latch_fresh other width)).trans (entered_read store width other)
  change success.key ∉ (lifted other width).storageKeys
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact separate

end

end QuantumAlg.ClassicalRoutines.GF2.Native
