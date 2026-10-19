/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Echelon
import all QuantumAlg.Components.Classical.GF2.Native.Load.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Space

/-!
# Actual live space of the full matrix-reduction prefix

The initialization row word is released before column searches. Searches
reuse their two latches and separate row/column masks across all columns.
The original loading word is likewise released before reduction begins.
The bounds retain the complete original context and every storage role.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

private lemma clearBody_resident
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (path : (pivotRowsClearBody rows zero).Path) :
    (pivotRowsClearBody rows zero).peakResidentSpace path ≤ ctx.residentSpace :=
  Circuit.forRange_resident_le width _ _ le_rfl
    (fun column current => by
      unfold BitWord.instruction
      exact (Circuit.peakResidentSpace_classical
        (BitWord.selectedApplication (execution := model)
          (pivotRowWriteOp rows zero column)) current).le) path

/-- Original pivot-row initialization adds one real row word to all existing resident storage. -/
lemma gf2ClearPivotRows_resident_le
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (path : (clearPivotRows rows).Path) :
    (clearPivotRows rows).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord rowCount) + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh (placedPivotRowsClear rows) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _) (clearBody_resident _ _ path)

/-- The initialization word and column workspaces are reused throughout the matrix. -/
lemma gf2ReduceMatrix_resident_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width))
    (path : (reduceMatrix matrix used rows columns).Path) :
    (reduceMatrix matrix used rows columns).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace)) := by
  have entry : ctx.residentSpace ≤ pivotMaskSpace (model := model) rowCount width +
      (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace)) := by
    intro axis
    change ctx.residentSpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))
    omega
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
    (.seq (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (.seq (clearPivotRows rows)
        (Circuit.forRange width (reduceColumn matrix used rows columns)))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le entry (SpacePool.max_le ?_
    (Circuit.forRange_resident_le width _ _ entry
      (gf2ReduceColumn_resident_le matrix used rows columns) path.2.2.2)))
  refine (gf2ClearPivotRows_resident_le rows path.2.2.1).trans ?_
  intro axis
  change SpacePool.ofShape (.unsignedWord rowCount) axis + ctx.residentSpace axis ≤
    max (SpacePool.ofShape (.unsignedWord rowCount) axis)
      (SpacePool.ofShape (.unsignedWord width) axis) +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))
  omega

/-- The original loader word is released before the complete reduction workspace is opened. -/
lemma gf2LoadAndReduce_resident_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width))
    (path : (loadAndReduce input matrix used rows columns).Path) :
    (loadAndReduce input matrix used rows columns).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace)) := by
  refine (Circuit.peakResidentSpace_seq (loadMatrix input matrix)
    (reduceMatrix matrix used rows columns) path).le.trans ?_
  refine SpacePool.max_le ?_ (gf2ReduceMatrix_resident_le matrix used rows columns path.2)
  refine (gf2LoadMatrix_resident_le input matrix path.1).trans ?_
  intro axis
  change SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis ≤
    max (SpacePool.ofShape (.unsignedWord rowCount) axis)
      (SpacePool.ofShape (.unsignedWord width) axis) +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))
  omega

private lemma clearBody_auxiliary
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (path : (pivotRowsClearBody rows zero).Path) :
    (pivotRowsClearBody rows zero).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  Circuit.forRange_auxiliary_le width _ _ le_rfl
    (fun column current => by
      unfold BitWord.instruction
      exact (Circuit.peakAuxiliarySpace_classical
        (BitWord.selectedApplication (execution := model)
          (pivotRowWriteOp rows zero column)) current).le) path

/-- Original pivot-row initialization adds one real row word to all existing auxiliary storage. -/
lemma gf2ClearPivotRows_auxiliary_le
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (path : (clearPivotRows rows).Path) :
    (clearPivotRows rows).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord rowCount) + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh (placedPivotRowsClear rows) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _) (clearBody_auxiliary _ _ path)

/-- The initialization word and column workspaces are reused throughout the matrix. -/
lemma gf2ReduceMatrix_auxiliary_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width))
    (path : (reduceMatrix matrix used rows columns).Path) :
    (reduceMatrix matrix used rows columns).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace)) := by
  have entry : ctx.auxiliarySpace ≤ pivotMaskSpace (model := model) rowCount width +
      (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace)) := by
    intro axis
    change ctx.auxiliarySpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))
    omega
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
    (.seq (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (.seq (clearPivotRows rows)
        (Circuit.forRange width (reduceColumn matrix used rows columns)))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le entry (SpacePool.max_le ?_
    (Circuit.forRange_auxiliary_le width _ _ entry
      (gf2ReduceColumn_auxiliary_le matrix used rows columns) path.2.2.2)))
  refine (gf2ClearPivotRows_auxiliary_le rows path.2.2.1).trans ?_
  intro axis
  change SpacePool.ofShape (.unsignedWord rowCount) axis + ctx.auxiliarySpace axis ≤
    max (SpacePool.ofShape (.unsignedWord rowCount) axis)
      (SpacePool.ofShape (.unsignedWord width) axis) +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))
  omega

/-- The original loader word is released before the complete reduction workspace is opened. -/
lemma gf2LoadAndReduce_auxiliary_le
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns : CWriteRef ctx (.unsignedWord width))
    (path : (loadAndReduce input matrix used rows columns).Path) :
    (loadAndReduce input matrix used rows columns).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace)) := by
  refine (Circuit.peakAuxiliarySpace_seq (loadMatrix input matrix)
    (reduceMatrix matrix used rows columns) path).le.trans ?_
  refine SpacePool.max_le ?_ (gf2ReduceMatrix_auxiliary_le matrix used rows columns path.2)
  refine (gf2LoadMatrix_auxiliary_le input matrix path.1).trans ?_
  intro axis
  change SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis ≤
    max (SpacePool.ofShape (.unsignedWord rowCount) axis)
      (SpacePool.ofShape (.unsignedWord width) axis) +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))
  omega

end QuantumAlg.ClassicalRoutines.GF2.Native
