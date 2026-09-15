/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision.Semantics
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Values of the actual stored GF(2) decisions

Every equality is evaluated from the chronological store, followed by the
original stored-bit branch and both charged failure instructions. The local
latch separation is supplied by the real lexical scope. Neither the zero
word nor the incoming success bit is silently initialized by these lemmas.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

private theorem shapes_ne {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (different : left ≠ right) : output.key ≠ other.key := by
  intro same
  exact different (CStorageRef.storageRef_shape_eq_of_key output.toCStorageRef
    other.toCStorageRef same)

/-- Both actual failure instructions finish with the original success bit false. -/
theorem gf2MarkFailure_success (success : CWriteRef ctx .bit) (store : Store ctx) :
    (markFailureStep success store).1.read (.storage success.toCStorageRef) = .bit false := by
  change ((store.applyOp (pivotRejectedOp success)).applyOp (pivotClearOp success)).read _ = _
  refine (Store.read_applyOp_output _ (pivotClearOp success)).trans ?_
  have selfXor (value : CShape.Value .bit) :
      Resource.BitOpcode.eval .xor (.product value value) = .bit false := by
    cases value with
    | bit value => cases value <;> rfl
  exact selfXor _

/-- The original failure marker preserves every read outside its actual bit destination. -/
theorem gf2MarkFailure_read_other (success : CWriteRef ctx .bit) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (markFailureStep success store).1.read other = store.read other := by
  change ((store.applyOp (pivotRejectedOp success)).applyOp (pivotClearOp success)).read _ = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotClearOp success) other separate,
    Store.read_applyOp_of_not_mem_storageKeys _ (pivotRejectedOp success) other separate]

private theorem choice_success (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) :
    ((decisionChoiceStep reject success value store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool && (value.toBool != reject)) := by
  cases value with
  | bit value =>
    cases reject <;> cases value <;>
      simp [decisionChoiceStep, gf2MarkFailure_success, CShape.Value.toBool]

private theorem choice_read (reject : Bool) (success : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) {shape : CShape}
    (other : CInputRef ctx shape) (separate : success.key ∉ other.storageKeys) :
    (decisionChoiceStep reject success value store).1.read other = store.read other := by
  cases value with
  | bit value =>
    cases reject <;> cases value
    · exact gf2MarkFailure_read_other success store other separate
    · rfl
    · rfl
    · exact gf2MarkFailure_read_other success store other separate

private theorem equality_read (left right : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (decisionEqualityOp left right flag)).read (.storage flag.toCStorageRef) =
      .bit (decide ((store.read (.storage left.toCStorageRef)).toNat =
        (store.read (.storage right.toCStorageRef)).toNat)) :=
  Store.read_applyOp_output store (decisionEqualityOp left right flag)

/-- The real equality latch preserves incoming success exactly on the accepting branch. -/
theorem gf2DecisionTest_success (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (separate : flag.key ≠ success.key) (store : Store ctx) :
    ((decisionTestStep reject left right success flag store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        (decide ((store.read (.storage left.toCStorageRef)).toNat =
          (store.read (.storage right.toCStorageRef)).toNat) != reject)) := by
  change ((decisionChoiceStep reject success
    ((store.applyOp (decisionEqualityOp left right flag)).read (.storage flag.toCStorageRef))
    (store.applyOp (decisionEqualityOp left right flag))).1.read _).toBool = _
  rw [equality_read, choice_success,
    Store.read_applyOp_of_not_mem_storageKeys _ (decisionEqualityOp left right flag)
      (.storage success.toCStorageRef) (avoids flag success separate)]
  rfl

/-- The equality and branch preserve structural reads outside both actual bit writes. -/
theorem gf2DecisionTest_read_other (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (successFree : success.key ∉ other.storageKeys) (flagFree : flag.key ∉ other.storageKeys) :
    (decisionTestStep reject left right success flag store).1.read other = store.read other := by
  change (decisionChoiceStep reject success
    ((store.applyOp (decisionEqualityOp left right flag)).read (.storage flag.toCStorageRef))
    (store.applyOp (decisionEqualityOp left right flag))).1.read _ = _
  rw [choice_read _ _ _ _ other successFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (decisionEqualityOp left right flag)
      other flagFree]

end

end QuantumAlg.ClassicalRoutines.GF2.Native
