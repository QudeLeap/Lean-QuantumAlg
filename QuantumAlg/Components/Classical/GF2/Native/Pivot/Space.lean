/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Resources

/-!
# Actual pivot-search lexical space

A complete column allocates the original two bit latches once. Selected
row and column masks are separate scopes, so only their maximum contributes
to the bound. Every original live entry and its storage role stays counted.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)

/-- The five selected stages reuse their real caller context and sequential mask scopes. -/
lemma gf2SelectPivot_resident_le (row : Fin rowCount) (column : Fin width)
    (path : (selectPivot matrix used rows columns found sink row column).Path) :
    (selectPivot matrix used rows columns found sink row column).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace := by
  have entry : ctx.residentSpace ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (.seq (materializePivotRow used rows row column)
        (.seq (materializePivotColumn columns column)
          (eliminateWithPivot matrix row column)))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq,
    Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le entry (SpacePool.max_le ?_
    (SpacePool.max_le ?_ ?_)))
  · exact (gf2MaterializePivotRow_resident_le used rows row column path.2.2.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (gf2MaterializePivotColumn_resident_le columns column path.2.2.2.1).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  · exact (gf2EliminateWithPivot_resident matrix row column path.2.2.2.2).le.trans entry

/-- Every actual row decision has the same complete resident allowance. -/
lemma gf2PivotProbeRow_resident_le (row : Fin rowCount) (column : Fin width)
    (path : (pivotProbeRow matrix used rows columns found sink row column).Path) :
    (pivotProbeRow matrix used rows columns found sink row column).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace := by
  have unchanged : SpacePool.max ctx.residentSpace 0 ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace :=
    (SpacePool.max_zero _).le.trans (fun _axis => Nat.le_add_left _ _)
  rcases path with ⟨value, path⟩
  cases value
  rename_i isFound
  cases isFound
  · rcases path with ⟨value, path⟩
    cases value
    rename_i isUsed
    cases isUsed
    · rcases path with ⟨value, path⟩
      cases value
      rename_i isSet
      cases isSet
      · exact unchanged
      · exact gf2SelectPivot_resident_le matrix used rows columns found sink row column path
    · exact unchanged
  · exact unchanged

/-- The increasing row scan reuses its mask space independently of row count. -/
lemma gf2ReduceColumnBody_resident_le (column : Fin width)
    (path : (reduceColumnBody matrix used rows columns found sink column).Path) :
    (reduceColumnBody matrix used rows columns found sink column).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace := by
  have entry : ctx.residentSpace ≤
      pivotMaskSpace (model := model) rowCount width + ctx.residentSpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakResidentSpace_seq
    (BitWord.instruction (execution := model) (pivotClearOp found))
    (.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice sink))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical, Circuit.peakResidentSpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le
    (Circuit.forRange_resident_le rowCount _ _ entry
      (fun row => gf2PivotProbeRow_resident_le matrix used rows columns found sink row column)
      path.2.1) ?_)
  rcases path.2.2 with ⟨value, last⟩
  cases value
  rename_i isFound
  cases isFound <;> exact (SpacePool.max_zero _).le.trans entry

/-- Both real bit latches and the maximum mask scope include all original resident entries. -/
lemma gf2ReduceColumn_resident_le (column : Fin width)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).peakResidentSpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.residentSpace)) := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (scopedPivotSearch matrix used rows columns column) path).le.trans
      ?_
  refine SpacePool.max_le ?_ ?_
  · intro axis
    change ctx.residentSpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))
    omega
  · refine (Circuit.peakResidentSpace_workspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh
      (placedPivotSearch matrix used rows columns column) path).le.trans ?_
    refine SpacePool.max_le ?_ (gf2ReduceColumnBody_resident_le _ _ _ _ _ _ column path)
    intro axis
    change SpacePool.ofShape .bit axis + ctx.residentSpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis))
    omega

/-- The five selected stages reuse their real caller context and sequential mask scopes. -/
lemma gf2SelectPivot_auxiliary_le (row : Fin rowCount) (column : Fin width)
    (path : (selectPivot matrix used rows columns found sink row column).Path) :
    (selectPivot matrix used rows columns found sink row column).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace := by
  have entry : ctx.auxiliarySpace ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (.seq (materializePivotRow used rows row column)
        (.seq (materializePivotColumn columns column)
          (eliminateWithPivot matrix row column)))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq,
    Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le entry (SpacePool.max_le ?_
    (SpacePool.max_le ?_ ?_)))
  · exact (gf2MaterializePivotRow_auxiliary_le used rows row column path.2.2.1).trans
      (add_le_add (SpacePool.le_max_left _ _) le_rfl)
  · exact (gf2MaterializePivotColumn_auxiliary_le columns column path.2.2.2.1).trans
      (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  · exact (gf2EliminateWithPivot_auxiliary matrix row column path.2.2.2.2).le.trans entry

/-- Every actual row decision has the same complete auxiliary allowance. -/
lemma gf2PivotProbeRow_auxiliary_le (row : Fin rowCount) (column : Fin width)
    (path : (pivotProbeRow matrix used rows columns found sink row column).Path) :
    (pivotProbeRow matrix used rows columns found sink row column).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace := by
  have unchanged : SpacePool.max ctx.auxiliarySpace 0 ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace :=
    (SpacePool.max_zero _).le.trans (fun _axis => Nat.le_add_left _ _)
  rcases path with ⟨value, path⟩
  cases value
  rename_i isFound
  cases isFound
  · rcases path with ⟨value, path⟩
    cases value
    rename_i isUsed
    cases isUsed
    · rcases path with ⟨value, path⟩
      cases value
      rename_i isSet
      cases isSet
      · exact unchanged
      · exact gf2SelectPivot_auxiliary_le matrix used rows columns found sink row column path
    · exact unchanged
  · exact unchanged

/-- The increasing row scan reuses its mask space independently of row count. -/
lemma gf2ReduceColumnBody_auxiliary_le (column : Fin width)
    (path : (reduceColumnBody matrix used rows columns found sink column).Path) :
    (reduceColumnBody matrix used rows columns found sink column).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace := by
  have entry : ctx.auxiliarySpace ≤
      pivotMaskSpace (model := model) rowCount width + ctx.auxiliarySpace :=
    fun _axis => Nat.le_add_left _ _
  refine (Circuit.peakAuxiliarySpace_seq
    (BitWord.instruction (execution := model) (pivotClearOp found))
    (.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column))
      (.branch (.storage found.toCStorageRef) (pivotAbsentChoice sink))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical, Circuit.peakAuxiliarySpace_seq]
  refine SpacePool.max_le entry (SpacePool.max_le
    (Circuit.forRange_auxiliary_le rowCount _ _ entry
      (fun row => gf2PivotProbeRow_auxiliary_le matrix used rows columns found sink row column)
      path.2.1) ?_)
  rcases path.2.2 with ⟨value, last⟩
  cases value
  rename_i isFound
  cases isFound <;> exact (SpacePool.max_zero _).le.trans entry

/-- Both real bit latches and the maximum mask scope include all original auxiliary entries. -/
lemma gf2ReduceColumn_auxiliary_le (column : Fin width)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).peakAuxiliarySpace path ≤
      pivotMaskSpace (model := model) rowCount width +
        (SpacePool.ofShape .bit + (SpacePool.ofShape .bit + ctx.auxiliarySpace)) := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey .bit
    ctx.canonicalFreshKey_fresh (scopedPivotSearch matrix used rows columns column) path).le.trans
      ?_
  refine SpacePool.max_le ?_ ?_
  · intro axis
    change ctx.auxiliarySpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))
    omega
  · refine (Circuit.peakAuxiliarySpace_workspace (pivotSinkContext ctx).canonicalFreshKey .bit
      (pivotSinkContext ctx).canonicalFreshKey_fresh
      (placedPivotSearch matrix used rows columns column) path).le.trans ?_
    refine SpacePool.max_le ?_ (gf2ReduceColumnBody_auxiliary_le _ _ _ _ _ _ column path)
    intro axis
    change SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis ≤
      pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis))
    omega

end QuantumAlg.ClassicalRoutines.GF2.Native
