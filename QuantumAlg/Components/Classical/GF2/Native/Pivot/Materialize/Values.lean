/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Frame
import all QuantumAlg.Core.Execution.Store.Ext
import all QuantumAlg.Util.Classical.GF2

/-!
# Original numerical values of the actual pivot masks

The original power loader writes the one-hot word at the reversed physical
coordinate. Real OR and vector-write instructions then update the used rows,
selected row record and selected columns. Their lexical masks are fresh by
construction, and word/vector shapes separate the two row destinations.
No initial mask, zero workspace or caller separation is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem word_eq_of_nat (left right : CShape.Value (.unsignedWord width))
    (same : left.toNat = right.toNat) : left = right := by
  cases left with
  | unsignedWord left =>
      cases right with
      | unsignedWord right => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

private theorem word_vector_ne {size count : Nat} {shape : CShape}
    (word : CWriteRef ctx (.unsignedWord size))
    (vector : CWriteRef ctx (.fixedVector count shape)) :
    word.key ≠ vector.key := by
  intro same
  have impossible := CStorageRef.storageRef_shape_eq_of_key word.toCStorageRef
    vector.toCStorageRef same
  cases impossible

private theorem or_read (output mask : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    ((store.applyOp (pivotOrOp output mask)).read (.storage output.toCStorageRef)).toNat =
      (store.read (.storage output.toCStorageRef)).toNat |||
        (store.read (.storage mask.toCStorageRef)).toNat := by
  simp only [Store.applyOp, pivotOrOp, ClassicalOp.outputRef, Store.read_write_same,
    ClassicalOp.inputRef, ClassicalOp.eval_wordBinary]
  change (_ ||| _) % 2 ^ width = _
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow
    (store.read (.storage output.toCStorageRef)).toNat_lt
    (store.read (.storage mask.toCStorageRef)).toNat_lt)

private theorem loaded_mask (index : Fin width) (mask : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (Word.PowerOfTwo.step (width - 1 - index.val) mask store).1.read
      (.storage mask.toCStorageRef) =
        .unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun current => decide (current = index))) := by
  apply word_eq_of_nat
  rw [Word.PowerOfTwo.into_read]
  change 2 ^ (width - 1 - index.val) % 2 ^ width =
    (ClassicalAlgorithms.GF2.wordOfLogicalBits (fun current => decide (current = index))).val
  have reversed : width - 1 - index.val = (Fin.rev index).val := by
    rw [Fin.val_rev]
    omega
  rw [reversed]
  rw [ClassicalAlgorithms.GF2.wordOfLogicalBits_singleton_val]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (Fin.rev index).isLt)

private theorem rowBody_used (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (store : Store ctx) (separate : mask.key ≠ used.key) :
    ((pivotRowBodyStep used rows mask pivot column store).1.read
      (.storage used.toCStorageRef)).toNat =
        (store.read (.storage used.toCStorageRef)).toNat ||| 2 ^ (Fin.rev pivot).val := by
  have rowsFree : rows.key ∉ (CInputRef.storage used.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using (word_vector_ne used rows).symm
  have maskFree : mask.key ∉ (CInputRef.storage used.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using separate
  change ((((Word.PowerOfTwo.step (rowCount - 1 - pivot.val) mask store).1.applyOp
    (pivotOrOp used mask)).applyOp (pivotRowWriteOp rows mask column)).read
      (.storage used.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotRowWriteOp rows mask column) _ rowsFree,
    or_read, Word.PowerOfTwo.into_callerFrame _ mask store _ maskFree, loaded_mask]
  change _ ||| (ClassicalAlgorithms.GF2.wordOfLogicalBits
    (fun current => decide (current = pivot))).val = _
  rw [ClassicalAlgorithms.GF2.wordOfLogicalBits_singleton_val]

private theorem rowBody_rows (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (store : Store ctx) (separate : mask.key ≠ used.key) :
    (pivotRowBodyStep used rows mask pivot column store).1.read (.storage rows.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage rows.toCStorageRef)) column
        (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun current => decide (current = pivot)))) := by
  let loaded := (Word.PowerOfTwo.step (rowCount - 1 - pivot.val) mask store).1
  have usedFree : used.key ∉ (CInputRef.storage rows.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using word_vector_ne used rows
  have maskFree : mask.key ∉ (CInputRef.storage rows.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using word_vector_ne mask rows
  have otherFree : used.key ∉ (CInputRef.storage mask.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using separate.symm
  have rowsValue : (loaded.applyOp (pivotOrOp used mask)).read (.storage rows.toCStorageRef) =
      store.read (.storage rows.toCStorageRef) :=
    (Store.read_applyOp_of_not_mem_storageKeys loaded (pivotOrOp used mask) _ usedFree).trans
      (Word.PowerOfTwo.into_callerFrame _ mask store _ maskFree)
  have maskValue := Store.read_applyOp_of_not_mem_storageKeys loaded (pivotOrOp used mask)
    (.storage mask.toCStorageRef) otherFree
  change ((loaded.applyOp (pivotOrOp used mask)).applyOp (pivotRowWriteOp rows mask column)).read
    (.storage rows.toCStorageRef) = _
  refine (Store.read_applyOp_output _ (pivotRowWriteOp rows mask column)).trans ?_
  change CShape.vectorWrite
    ((loaded.applyOp (pivotOrOp used mask)).read (.storage rows.toCStorageRef)) column
    ((loaded.applyOp (pivotOrOp used mask)).read (.storage mask.toCStorageRef)) = _
  rw [rowsValue, maskValue, loaded_mask]

private theorem columnBody_columns (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) (separate : mask.key ≠ output.key) :
    ((pivotColumnBodyStep output mask column store).1.read (.storage output.toCStorageRef)).toNat =
      (store.read (.storage output.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val := by
  have maskFree : mask.key ∉ (CInputRef.storage output.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using separate
  change (((Word.PowerOfTwo.step (width - 1 - column.val) mask store).1.applyOp
    (pivotOrOp output mask)).read (.storage output.toCStorageRef)).toNat = _
  rw [or_read, Word.PowerOfTwo.into_callerFrame _ mask store _ maskFree, loaded_mask]
  change _ ||| (ClassicalAlgorithms.GF2.wordOfLogicalBits
    (fun current => decide (current = column))).val = _
  rw [ClassicalAlgorithms.GF2.wordOfLogicalBits_singleton_val]

private theorem mask_ne {shape : CShape} (output : CWriteRef ctx shape) (maskWidth : Nat) :
    (pivotMaskCell ctx maskWidth).key ≠ output.key := by
  intro same
  apply ctx.canonicalFreshKey_fresh
  change ctx.canonicalFreshKey = output.key at same
  rw [same]
  exact CInputRef.storageKeys_subset_context (.storage output.toCStorageRef)
    (by simp [CInputRef.storageKeys])

/-- The real lexical row mask marks exactly the original logical pivot row as used. -/
theorem gf2MaterializePivotRow_used (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    ((materializePivotRowStep used rows pivot column store).1.read
      (.storage used.toCStorageRef)).toNat =
        (store.read (.storage used.toCStorageRef)).toNat ||| 2 ^ (Fin.rev pivot).val := by
  change ((Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh _).read _).toNat = _
  rw [Store.read_popWorkspace_underWorkspace]
  have written := rowBody_used
    (used.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) pivot column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (mask_ne used rowCount)
  refine written.trans ?_
  exact congrArg (fun value : CShape.Value (.unsignedWord rowCount) =>
    value.toNat ||| 2 ^ (Fin.rev pivot).val)
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh (.storage used.toCStorageRef))

/-- The original row record is the actual vector update by the MSB-first one-hot word. -/
theorem gf2MaterializePivotRow_rows (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (materializePivotRowStep used rows pivot column store).1.read (.storage rows.toCStorageRef) =
      CShape.vectorWrite (store.read (.storage rows.toCStorageRef)) column
        (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
          (fun current => decide (current = pivot)))) := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  have written := rowBody_rows
    (used.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh)
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) pivot column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (mask_ne used rowCount)
  refine written.trans ?_
  exact congrArg (fun value => CShape.vectorWrite value column
    (.unsignedWord (ClassicalAlgorithms.GF2.wordOfLogicalBits
      (fun current => decide (current = pivot)))))
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh (.storage rows.toCStorageRef))

/-- The real lexical column mask marks exactly the selected original logical column. -/
theorem gf2MaterializePivotColumn_columns (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) :
    ((materializePivotColumnStep output column store).1.read
      (.storage output.toCStorageRef)).toNat =
        (store.read (.storage output.toCStorageRef)).toNat ||| 2 ^ (Fin.rev column).val := by
  change ((Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read _).toNat = _
  rw [Store.read_popWorkspace_underWorkspace]
  have written := columnBody_columns
    (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx width) column
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) (mask_ne output width)
  refine written.trans ?_
  exact congrArg (fun value : CShape.Value (.unsignedWord width) =>
    value.toNat ||| 2 ^ (Fin.rev column).val)
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh (.storage output.toCStorageRef))

end

end QuantumAlg.ClassicalRoutines.GF2.Native
