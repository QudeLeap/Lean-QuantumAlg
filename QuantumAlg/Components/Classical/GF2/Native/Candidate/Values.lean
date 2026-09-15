/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Values

/-!
# Actual stored values of original GF(2) candidate contributions

The reduced row is ANDed with the current free word and compared with the
current zero source. The selected contribution then uses the existing real
column-mask scope. Internal masked-word and equality cells are fresh by their
actual allocation; original caller words may alias and need not initially be
zero. Every caller read outside the candidate destination is preserved.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem avoids {left right : CShape} (output : CWriteRef ctx left)
    (other : CWriteRef ctx right) (separate : output.key ≠ other.key) :
    output.key ∉ (CInputRef.storage other.toCStorageRef).storageKeys := by
  simpa only [CInputRef.storageKeys, List.mem_singleton] using separate

private theorem bit_word_ne (flag : CWriteRef ctx .bit)
    (word : CWriteRef ctx (.unsignedWord width)) : flag.key ≠ word.key := by
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key flag.toCStorageRef
    word.toCStorageRef same
  cases impossible

private theorem coefficient_other (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (candidateCoefficientChoiceStep candidate column value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_read_other candidate column store other separate
      · rfl

private theorem rowBody_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (candidateFree : candidate.key ∉ other.storageKeys)
    (workFree : work.key ∉ other.storageKeys) (flagFree : flag.key ∉ other.storageKeys) :
    (candidateRowBodyStep matrix free candidate zero work flag row column store).1.read other =
      store.read other := by
  change (candidateCoefficientChoiceStep candidate column _
    ((store.applyOp (candidateMaskOp matrix free work row)).applyOp
      (decisionEqualityOp work zero flag))).1.read other = _
  rw [coefficient_other candidate column _ _ other candidateFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (decisionEqualityOp work zero flag) _ flagFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (candidateMaskOp matrix free work row) _ workFree]

private theorem mask_read
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free work : CWriteRef ctx (.unsignedWord width)) (row : Fin rowCount) (store : Store ctx) :
    (store.applyOp (candidateMaskOp matrix free work row)).read (.storage work.toCStorageRef) =
      CShape.wordBitAnd width ((store.read (.storage matrix.toCStorageRef)).get row)
        (store.read (.storage free.toCStorageRef)) := by
  exact Store.read_applyOp_output store (candidateMaskOp matrix free work row)

private theorem equality_read (left right : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (decisionEqualityOp left right flag)).read (.storage flag.toCStorageRef) =
      .bit (decide ((store.read (.storage left.toCStorageRef)).toNat =
        (store.read (.storage right.toCStorageRef)).toNat)) := by
  exact Store.read_applyOp_output store (decisionEqualityOp left right flag)

private theorem rowBody_candidate
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    (workCandidate : work.key ≠ candidate.key) (workZero : work.key ≠ zero.key) :
    ((candidateRowBodyStep matrix free candidate zero work flag row column store).1.read
      (.storage candidate.toCStorageRef)).toNat =
      if (CShape.wordBitAnd width ((store.read (.storage matrix.toCStorageRef)).get row)
          (store.read (.storage free.toCStorageRef))).toNat =
            (store.read (.storage zero.toCStorageRef)).toNat then
        (store.read (.storage candidate.toCStorageRef)).toNat else
        (store.read (.storage candidate.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val := by
  let masked := store.applyOp (candidateMaskOp matrix free work row)
  let tested := masked.applyOp (decisionEqualityOp work zero flag)
  have zeroSame : masked.read (.storage zero.toCStorageRef) =
      store.read (.storage zero.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (candidateMaskOp matrix free work row) _
      (avoids work zero workZero)
  have candidateSame : tested.read (.storage candidate.toCStorageRef) =
      store.read (.storage candidate.toCStorageRef) :=
    (Store.read_applyOp_of_not_mem_storageKeys masked (decisionEqualityOp work zero flag) _
      (avoids flag candidate (bit_word_ne flag candidate))).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (candidateMaskOp matrix free work row) _
          (avoids work candidate workCandidate))
  have flagValue := equality_read work zero flag masked
  rw [zeroSame, mask_read] at flagValue
  change ((candidateCoefficientChoiceStep candidate column
    (tested.read (.storage flag.toCStorageRef)) tested).1.read _).toNat = _
  rw [flagValue]
  by_cases equal :
      (CShape.wordBitAnd width ((store.read (.storage matrix.toCStorageRef)).get row)
        (store.read (.storage free.toCStorageRef))).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat
  · rw [if_pos equal, decide_eq_true equal]
    exact congrArg CShape.Value.toNat candidateSame
  · rw [if_neg equal, decide_eq_false equal]
    exact (gf2MaterializePivotColumn_columns candidate column tested).trans
      (congrArg (fun value : CShape.Value (.unsignedWord width) =>
        value.toNat ||| 2 ^ (Fin.rev column).val) candidateSame)

private theorem mask_fresh {shape : CShape} (other : CInputRef ctx shape) :
    (pivotMaskCell ctx width).key ∉
      (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
        ctx.canonicalFreshKey_fresh).storageKeys := by
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

private theorem flag_fresh {shape : CShape} (other : CInputRef ctx shape) :
    (pivotLatch ctx).key ∉
      (other.underWorkspace ctx.canonicalFreshKey .bit
        ctx.canonicalFreshKey_fresh).storageKeys := by
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

/-- Both real row scopes preserve every caller read outside the actual candidate destination. -/
theorem gf2CandidateRowSelected_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : candidate.key ∉ other.storageKeys) :
    (candidateRowSelectedStep matrix free candidate zero row column store).1.read other =
      store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read other = _
  rw [Store.read_popWorkspace_underWorkspace]
  change (Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
    (pivotMaskContext ctx width).canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  refine (rowBody_other (decisionWrite width matrix) (decisionWrite width free)
    (decisionWrite width candidate) (decisionWrite width zero) (decisionWork ctx width)
    (pivotLatch (pivotMaskContext ctx width)) row column _ _ ?_ ?_ ?_).trans ?_
  · rw [CInputRef.storageKeys_underWorkspace, CInputRef.storageKeys_underWorkspace]
    exact separate
  · rw [CInputRef.storageKeys_underWorkspace]
    exact mask_fresh other
  · exact flag_fresh _
  · rw [Store.read_pushWorkspace_underWorkspace, Store.read_pushWorkspace_underWorkspace]

private theorem work_ne {shape : CShape} (output : CWriteRef ctx shape) :
    (decisionWork ctx width).key ≠ (decisionWrite width output).key := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  change ctx.canonicalFreshKey = output.key at same
  rw [same]
  exact CInputRef.storageKeys_subset_context (.storage output.toCStorageRef)
    (by simp [CInputRef.storageKeys])

private theorem both_read {shape : CShape} (output : CWriteRef ctx shape) (store : Store ctx) :
    ((store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh).pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey
        .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh).read
          (.storage (decisionWrite width output).toCStorageRef) =
            store.read (.storage output.toCStorageRef) := by
  refine (Store.read_pushWorkspace_underWorkspace _ _ _ _
    ((CInputRef.storage output.toCStorageRef).underWorkspace ctx.canonicalFreshKey
      (.unsignedWord width) ctx.canonicalFreshKey_fresh)).trans ?_
  exact Store.read_pushWorkspace_underWorkspace store _ _ _ (.storage output.toCStorageRef)

/-- The actual contribution tests the real current words, with all internal freshness discharged. -/
theorem gf2CandidateRowSelected_candidate
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero : CWriteRef ctx (.unsignedWord width))
    (row : Fin rowCount) (column : Fin width) (store : Store ctx) :
    ((candidateRowSelectedStep matrix free candidate zero row column store).1.read
      (.storage candidate.toCStorageRef)).toNat =
      if (CShape.wordBitAnd width ((store.read (.storage matrix.toCStorageRef)).get row)
          (store.read (.storage free.toCStorageRef))).toNat =
            (store.read (.storage zero.toCStorageRef)).toNat then
        (store.read (.storage candidate.toCStorageRef)).toNat else
        (store.read (.storage candidate.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val := by
  let entered := (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
  have actual := rowBody_candidate (decisionWrite width matrix) (decisionWrite width free)
    (decisionWrite width candidate) (decisionWrite width zero) (decisionWork ctx width)
    (pivotLatch (pivotMaskContext ctx width)) row column entered
    (work_ne candidate) (work_ne zero)
  change ((Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read _).toNat = _
  rw [Store.read_popWorkspace_underWorkspace]
  change ((Store.popWorkspace (pivotMaskContext ctx width).canonicalFreshKey .bit
    (pivotMaskContext ctx width).canonicalFreshKey_fresh _).read _).toNat = _
  rw [Store.read_popWorkspace_underWorkspace]
  change ((candidateRowBodyStep (decisionWrite width matrix) (decisionWrite width free)
    (decisionWrite width candidate) (decisionWrite width zero) (decisionWork ctx width)
    (pivotLatch (pivotMaskContext ctx width)) row column entered).1.read
      (.storage (decisionWrite width candidate).toCStorageRef)).toNat = _
  refine actual.trans ?_
  simp only [entered, both_read]

end

end QuantumAlg.ClassicalRoutines.GF2.Native
