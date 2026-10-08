/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual caller reads preserved by original pivot-mask scopes

Both original power loaders use genuinely fresh lexical words. After their
real OR and vector-write instructions, popping those words preserves every
structural caller read outside the actual destinations. The original output
references may alias; only the stated observed read must avoid their keys.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private theorem rowBody_read_other (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (usedFree : used.key ∉ other.storageKeys) (rowsFree : rows.key ∉ other.storageKeys)
    (maskFree : mask.key ∉ other.storageKeys) :
    (pivotRowBodyStep used rows mask pivot column store).1.read other = store.read other := by
  change (((Word.PowerOfTwo.step (rowCount - 1 - pivot.val) mask store).1.applyOp
    (pivotOrOp used mask)).applyOp (pivotRowWriteOp rows mask column)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotRowWriteOp rows mask column)
      other rowsFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (pivotOrOp used mask) other usedFree]
  exact Word.PowerOfTwo.into_callerFrame _ mask store other maskFree

private theorem columnBody_read_other (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (outputFree : output.key ∉ other.storageKeys) (maskFree : mask.key ∉ other.storageKeys) :
    (pivotColumnBodyStep output mask column store).1.read other = store.read other := by
  change ((Word.PowerOfTwo.step (width - 1 - column.val) mask store).1.applyOp
    (pivotOrOp output mask)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (pivotOrOp output mask) other outputFree]
  exact Word.PowerOfTwo.into_callerFrame _ mask store other maskFree

omit [BitWord.Selected model] in
private theorem mask_fresh {shape : CShape} (other : CInputRef ctx shape) (maskWidth : Nat) :
    (pivotMaskCell ctx maskWidth).key ∉
      (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord maskWidth)
        ctx.canonicalFreshKey_fresh).storageKeys := by
  rw [CInputRef.storageKeys_underWorkspace]
  exact fun present => ctx.canonicalFreshKey_fresh (other.storageKeys_subset_context present)

/-- The actual row-mask scope preserves every caller read outside its two real destinations. -/
theorem gf2MaterializePivotRow_read_other (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (usedFree : used.key ∉ other.storageKeys) (rowsFree : rows.key ∉ other.storageKeys) :
    (materializePivotRowStep used rows pivot column store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  refine (rowBody_read_other _ _ _ pivot column _
    (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) ?_ ?_ (mask_fresh other rowCount)).trans ?_
  · rw [CInputRef.storageKeys_underWorkspace]
    exact usedFree
  · rw [CInputRef.storageKeys_underWorkspace]
    exact rowsFree
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other

/-- The actual column-mask scope preserves every caller read outside its real OR destination. -/
theorem gf2MaterializePivotColumn_read_other (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (outputFree : output.key ∉ other.storageKeys) :
    (materializePivotColumnStep output column store).1.read other = store.read other := by
  change (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh _).read _ = _
  rw [Store.read_popWorkspace_underWorkspace]
  refine (columnBody_read_other _ _ column _
    (other.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
      ctx.canonicalFreshKey_fresh) ?_ (mask_fresh other width)).trans ?_
  · rw [CInputRef.storageKeys_underWorkspace]
    exact outputFree
  · exact Store.read_pushWorkspace_underWorkspace store _ _ _ other

end

end QuantumAlg.ClassicalRoutines.GF2.Native
