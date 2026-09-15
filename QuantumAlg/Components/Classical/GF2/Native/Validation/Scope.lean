/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Validation.Values
import all QuantumAlg.Components.Classical.GF2.Native.Decision.Values
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Original validation values through both actual temporary scopes

Parity is really cleared, every sample bit is checked in its original order,
and the stored parity controls the original failure instructions. The two
actual fresh bits supply every temporary separation condition. Incoming
success, the candidate and all caller samples may have arbitrary values.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

private theorem bit_word_ne (bit : CWriteRef ctx .bit)
    (word : CWriteRef ctx (.unsignedWord width)) : bit.key ≠ word.key := by
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key bit.toCStorageRef
    word.toCStorageRef same
  cases impossible

private theorem choice_success (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) :
    ((decisionChoiceStep true success value store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool && !value.toBool) := by
  cases value with
  | bit value =>
    cases value <;> simp [decisionChoiceStep, gf2MarkFailure_success, CShape.Value.toBool]

private theorem choice_read (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (decisionChoiceStep true success value store).1.read other = store.read other := by
  cases value with
  | bit value =>
    cases value
    · rfl
    · exact gf2MarkFailure_read_other success store other separate

private theorem clear_value (parity : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (pivotClearOp parity)).read (.storage parity.toCStorageRef) = .bit false := by
  refine (Store.read_applyOp_output store (pivotClearOp parity)).trans ?_
  change Resource.BitOpcode.eval .xor (.product (store.read (.storage parity.toCStorageRef))
    (store.read (.storage parity.toCStorageRef))) = _
  cases store.read (.storage parity.toCStorageRef) with
  | bit value => cases value <;> rfl

private theorem row_body_success
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount) (store : Store ctx)
    (separate : product.key ≠ parity.key)
    (parityFree : parity.key ∉ input.storageKeys) (productFree : product.key ∉ input.storageKeys)
    (paritySuccess : parity.key ≠ success.key) (productSuccess : product.key ≠ success.key)
    (rowWord candidateWord : ClassicalAlgorithms.Word width)
    (sampleValue : (store.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord))
    (candidateValue : store.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord) :
    ((validationRowBodyStep input candidate success parity product row store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        decide (ClassicalAlgorithms.GF2.dot rowWord candidateWord = 0)) := by
  let cleared := store.applyOp (pivotClearOp parity)
  let completed := (Circuit.forRangeRecord width
    (validationColumn input candidate parity product row)
    (validationColumnStep input candidate parity product row) cleared).1
  have inputSame : cleared.read input = store.read input :=
    Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp parity) input parityFree
  have candidateSame : cleared.read (.storage candidate.toCStorageRef) =
      .unsignedWord candidateWord :=
    (Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp parity)
      (.storage candidate.toCStorageRef)
      (avoids parity candidate (bit_word_ne parity candidate))).trans candidateValue
  have rowSame : (cleared.read input).get row =
      .bits (ClassicalAlgorithms.GF2.testBit rowWord) :=
    (congrArg (fun value => value.get row) inputSame).trans sampleValue
  have parityZero := gf2ValidationColumns_zero_iff input candidate parity product row cleared
    separate parityFree productFree rowWord candidateWord rowSame candidateSame
      (clear_value parity store)
  have successSame : completed.read (.storage success.toCStorageRef) =
      store.read (.storage success.toCStorageRef) :=
    (gf2ValidationColumns_read_other input candidate parity product row width id cleared
      (.storage success.toCStorageRef) (avoids parity success paritySuccess)
      (avoids product success productSuccess)).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp parity)
          (.storage success.toCStorageRef) (avoids parity success paritySuccess))
  have test : (!(completed.read (.storage parity.toCStorageRef)).toBool) =
      decide (ClassicalAlgorithms.GF2.dot rowWord candidateWord = 0) := by
    by_cases zero : ClassicalAlgorithms.GF2.dot rowWord candidateWord = 0
    · have bit : (completed.read (.storage parity.toCStorageRef)).toBool = false :=
        parityZero.mpr zero
      simp only [bit, Bool.not_false, zero, decide_true]
    · have bit : (completed.read (.storage parity.toCStorageRef)).toBool = true :=
        Bool.eq_true_of_not_eq_false (mt parityZero.mp zero)
      simp only [bit, Bool.not_true, zero, decide_false]
  change ((decisionChoiceStep true success (completed.read (.storage parity.toCStorageRef))
    completed).1.read (.storage success.toCStorageRef)).toBool = _
  rw [choice_success, successSame, test]

private theorem row_body_read
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (success parity product : CWriteRef ctx .bit) (row : Fin rowCount) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (successFree : success.key ∉ other.storageKeys)
    (parityFree : parity.key ∉ other.storageKeys)
    (productFree : product.key ∉ other.storageKeys) :
    (validationRowBodyStep input candidate success parity product row store).1.read other =
      store.read other := by
  dsimp only [validationRowBodyStep, Circuit.sequenceRecord]
  refine (choice_read success _ _ other successFree).trans ?_
  refine (gf2ValidationColumns_read_other input candidate parity product row width id _
    other parityFree productFree).trans ?_
  exact Store.read_applyOp_of_not_mem_storageKeys store (pivotClearOp parity) other parityFree

private def lifted {shape : CShape} (input : CInputRef ctx shape) :
    CInputRef (pivotSearchContext ctx) shape :=
  (input.underWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).underWorkspace
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh

private def entered (store : Store ctx) : Store (pivotSearchContext ctx) :=
  (store.pushWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).pushWorkspace
    (pivotSinkContext ctx).canonicalFreshKey .bit (pivotSinkContext ctx).canonicalFreshKey_fresh

private theorem entered_read (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) : (entered store).read (lifted input) = store.read input := by
  unfold entered lifted
  rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace]

private theorem exited_read (store : Store (pivotSearchContext ctx)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
      (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
        (pivotSinkContext ctx).canonicalFreshKey_fresh store)).read input =
      store.read (lifted input) := by
  rw [Store.read_popWorkspace_underWorkspace, Store.read_popWorkspace_underWorkspace]
  rfl

private theorem product_fresh {shape : CShape} (input : CInputRef ctx shape) :
    (pivotLatch (pivotSinkContext ctx)).key ∉ (lifted input).storageKeys := by
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => (pivotSinkContext ctx).canonicalFreshKey_fresh
    ((input.underWorkspace ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh).storageKeys_subset_context present)

private theorem parity_fresh {shape : CShape} (input : CInputRef ctx shape) :
    (validationParity ctx).key ∉ (lifted input).storageKeys := by
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (input.storageKeys_subset_context present)

private theorem product_separate :
    (pivotLatch (pivotSinkContext ctx)).key ≠ (validationParity ctx).key := by
  have fresh := (pivotSinkContext ctx).canonicalFreshKey_fresh
  intro same
  apply fresh
  change (pivotSinkContext ctx).canonicalFreshKey = (pivotLatch ctx).key at same
  rw [same]
  exact CInputRef.storageKeys_subset_context (.storage (pivotLatch ctx).toCStorageRef)
    (by simp [CInputRef.storageKeys])

private theorem parity_success (success : CWriteRef ctx .bit) :
    (validationParity ctx).key ≠ (pivotSearchWrite success).key := by
  have fresh := parity_fresh (.storage success.toCStorageRef)
  change _ ∉ [success.key] at fresh
  simpa only [List.mem_singleton, pivotSearchWrite, CWriteRef.underWorkspace,
    CStorageRef.underWorkspace] using fresh

private theorem product_success (success : CWriteRef ctx .bit) :
    (pivotLatch (pivotSinkContext ctx)).key ≠ (pivotSearchWrite success).key := by
  have fresh := product_fresh (.storage success.toCStorageRef)
  change _ ∉ [success.key] at fresh
  simpa only [List.mem_singleton, pivotSearchWrite, CWriteRef.underWorkspace,
    CStorageRef.underWorkspace] using fresh

/-- Both actual fresh scopes return success exactly for the original sample equation. -/
theorem gf2ValidationRow_success
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) :
    let word : ClassicalAlgorithms.Word width :=
      ⟨(store.read (.storage candidate.toCStorageRef)).toNat,
        (store.read (.storage candidate.toCStorageRef)).toNat_lt⟩
    ((validateRowStep input candidate success row store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        decide (ClassicalAlgorithms.GF2.dot (ClassicalAlgorithms.TerminalDecode.eval
          (TerminalDecode.decodeInput .bigEndian ((store.read input).get row))) word = 0)) := by
  let word : ClassicalAlgorithms.Word width :=
    ⟨(store.read (.storage candidate.toCStorageRef)).toNat,
      (store.read (.storage candidate.toCStorageRef)).toNat_lt⟩
  have candidateValue : store.read (.storage candidate.toCStorageRef) = .unsignedWord word := by
    dsimp only [word]
    cases store.read (.storage candidate.toCStorageRef)
    rfl
  have scopedCandidate : (entered store).read
      (.storage (pivotSearchWrite candidate).toCStorageRef) = .unsignedWord word :=
    (entered_read store (.storage candidate.toCStorageRef)).trans candidateValue
  have scopedSample : ((entered store).read (validationInput input)).get row =
      .bits (ClassicalAlgorithms.GF2.testBit (ClassicalAlgorithms.TerminalDecode.eval
        (TerminalDecode.decodeInput .bigEndian ((store.read input).get row)))) :=
    (congrArg (fun value => value.get row) (entered_read store input)).trans
      (gf2ValidationDecodedBits ((store.read input).get row))
  change ((Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh _)).read _).toBool = _
  rw [exited_read]
  refine (row_body_success (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row
    (entered store) product_separate (parity_fresh input) (product_fresh input)
    (parity_success success) (product_success success) _ word scopedSample scopedCandidate).trans ?_
  have scopedSuccess : (entered store).read (.storage (pivotSearchWrite success).toCStorageRef) =
      store.read (.storage success.toCStorageRef) :=
    entered_read store (.storage success.toCStorageRef)
  rw [scopedSuccess]

/-- Both original row scopes preserve every caller read outside the original success cell. -/
theorem gf2ValidationRow_read_other
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (candidate : CWriteRef ctx (.unsignedWord width)) (success : CWriteRef ctx .bit)
    (row : Fin rowCount) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : success.key ∉ other.storageKeys) :
    (validateRowStep input candidate success row store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh _)).read other = _
  rw [exited_read]
  refine (row_body_read (validationInput input) (pivotSearchWrite candidate)
    (pivotSearchWrite success) (validationParity ctx) (pivotLatch (pivotSinkContext ctx)) row
    (entered store) (lifted other) ?_ (parity_fresh other) (product_fresh other)).trans
      (entered_read store other)
  change success.key ∉ (lifted other).storageKeys
  unfold lifted
  rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
  exact separate

end

end QuantumAlg.ClassicalRoutines.GF2.Native
