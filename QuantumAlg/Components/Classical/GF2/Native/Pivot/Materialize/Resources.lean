/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize
import all QuantumAlg.Components.Classical.Word.PowerOfTwo.Resources
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Actual pivot-mask events, durations and lexical space

The formulas retain the complete original one-hot loaders and both real
record updates. Row and column masks have separate scopes; these theorems
charge each actual scope with the complete caller context.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The selected coordinate of a pivot-materialization operation. -/
def pivotMaterializeEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

/-- Exact row-mask instruction list, including the used-row OR and pivot-row vector write. -/
def pivotRowTrace (rowCount width : Nat) (pivot : Fin rowCount) :
    List (Resource.Event model) :=
  Word.PowerOfTwo.powerTrace (model := model) rowCount (rowCount - 1 - pivot.val) ++
    [pivotMaterializeEvent (model := model) (.wordBinary .bitOr rowCount),
      pivotMaterializeEvent (model := model) (.vector .write width rowCount)]

/-- Exact column-mask instruction list, including its pivot-column OR. -/
def pivotColumnTrace (width : Nat) (column : Fin width) :
    List (Resource.Event model) :=
  Word.PowerOfTwo.powerTrace (model := model) width (width - 1 - column.val) ++
    [pivotMaterializeEvent (model := model) (.wordBinary .bitOr width)]

private lemma power_duration (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (duration : Resource.Event model → Nat)
    (path : (Word.PowerOfTwo.into (model := model) count output).Path) :
    (Word.PowerOfTwo.into (model := model) count output).depth duration path =
      ((Word.PowerOfTwo.powerTrace (model := model) width count).map duration).sum := by
  change (Circuit.seq
    (Circuit.seq
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp output))
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.incrementOp output)))
    (Word.PowerOfTwo.shiftInto (model := model) count output)).Path at path
  change
    ((BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp output)).depth
        duration path.1.1 +
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.incrementOp output)).depth
        duration path.1.2) +
      (Word.PowerOfTwo.shiftInto (model := model) count output).depth duration path.2 = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  simp only [Word.PowerOfTwo.clearOp, Word.PowerOfTwo.incrementOp, ClassicalOp.label]
  unfold Word.PowerOfTwo.shiftInto BitWord.repeatInstruction
  have shiftDepth :
      (Circuit.iterate count
        (BitWord.instruction (execution := model)
          (Word.PowerOfTwo.shiftOp output))).depth duration path.2 =
        0 + ∑ _index : Fin count,
          duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .shiftLeft width))) := by
    change 0 + ∑ index : Fin count,
      (BitWord.instruction (execution := model)
        (Word.PowerOfTwo.shiftOp output)).depth duration (path.2 index) = _
    congr 1
    apply Finset.sum_congr rfl
    intro index _present
    rw [BitWord.bitWord_instruction_depth]
    rfl
  rw [shiftDepth]
  change (duration (pivotMaterializeEvent (model := model) (.wordBinary .bitXor width)) +
    duration (pivotMaterializeEvent (model := model) (.wordUnary .increment width))) +
      (0 + ∑ _index : Fin count,
        duration (pivotMaterializeEvent (model := model) (.wordUnary .shiftLeft width))) = _
  simp [pivotMaterializeEvent, Word.PowerOfTwo.powerTrace,
    Word.PowerOfTwo.shiftTrace, Nat.add_assoc]

/-- Actual row-mask paths emit exactly the original row-record instructions. -/
lemma gf2PivotRowBody_events (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (path : (pivotRowBody used rows mask pivot column).Path) :
    (pivotRowBody used rows mask pivot column).eventTrace path =
      pivotRowTrace (model := model) rowCount width pivot := by
  change (Circuit.seq
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (Circuit.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column)))).Path at path
  change (Word.PowerOfTwo.into (model := model)
      (rowCount - 1 - pivot.val) mask).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (pivotOrOp used mask)).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column)).eventTrace path.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  exact congrArg (fun events : List (Resource.Event model) =>
    events ++ [pivotMaterializeEvent (model := model) (.wordBinary .bitOr rowCount),
    pivotMaterializeEvent (model := model) (.vector .write width rowCount)])
    (Word.PowerOfTwo.into_events _ mask path.1)

/-- Every duration is charged in the original row-materialization order. -/
lemma gf2PivotRowBody_depth (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (pivotRowBody used rows mask pivot column).Path) :
    (pivotRowBody used rows mask pivot column).depth duration path =
      ((pivotRowTrace (model := model) rowCount width pivot).map duration).sum := by
  change (Circuit.seq
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (Circuit.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column)))).Path at path
  change (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (pivotOrOp used mask)).depth duration path.2.1 +
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column)).depth duration path.2.2) = _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  change (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask).depth
      duration path.1 +
    (duration (pivotMaterializeEvent (model := model) (.wordBinary .bitOr rowCount)) +
      duration (pivotMaterializeEvent (model := model) (.vector .write width rowCount))) = _
  rw [power_duration]
  simp only [pivotRowTrace, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Actual column-mask paths emit exactly the original loader and column OR. -/
lemma gf2PivotColumnBody_events (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (pivotColumnBody output mask column).Path) :
    (pivotColumnBody output mask column).eventTrace path =
      pivotColumnTrace (model := model) width column := by
  change (Circuit.seq
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask))).Path at path
  change (Word.PowerOfTwo.into (model := model)
      (width - 1 - column.val) mask).eventTrace path.1 ++
    (BitWord.instruction (execution := model)
      (pivotOrOp output mask)).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace]
  exact congrArg (fun events : List (Resource.Event model) =>
    events ++ [pivotMaterializeEvent (model := model) (.wordBinary .bitOr width)])
    (Word.PowerOfTwo.into_events _ mask path.1)

/-- Column-materialization depth is the duration sum of those exact original instructions. -/
lemma gf2PivotColumnBody_depth (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (pivotColumnBody output mask column).Path) :
    (pivotColumnBody output mask column).depth duration path =
      ((pivotColumnTrace (model := model) width column).map duration).sum := by
  change (Circuit.seq
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask))).Path at path
  change (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask).depth
      duration path.1 +
    (BitWord.instruction (execution := model) (pivotOrOp output mask)).depth
      duration path.2 = _
  rw [BitWord.bitWord_instruction_depth]
  change (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask).depth
      duration path.1 +
    duration (pivotMaterializeEvent (model := model) (.wordBinary .bitOr width)) = _
  rw [power_duration]
  simp only [pivotColumnTrace, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Row lexical allocation and release do not replace or add any native instruction. -/
lemma gf2MaterializePivotRow_events (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (materializePivotRow used rows pivot column).Path) :
    (materializePivotRow used rows pivot column).eventTrace path =
      pivotRowTrace (model := model) rowCount width pivot :=
  gf2PivotRowBody_events _ _ _ pivot column path

/-- The complete row scope retains the exact original duration sum. -/
lemma gf2MaterializePivotRow_depth (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (materializePivotRow used rows pivot column).Path) :
    (materializePivotRow used rows pivot column).depth duration path =
      ((pivotRowTrace (model := model) rowCount width pivot).map duration).sum :=
  gf2PivotRowBody_depth _ _ _ pivot column duration path

/-- Column allocation and release preserve the exact original instruction sequence. -/
lemma gf2MaterializePivotColumn_events (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (materializePivotColumn output column).Path) :
    (materializePivotColumn output column).eventTrace path =
      pivotColumnTrace (model := model) width column :=
  gf2PivotColumnBody_events _ _ column path

/-- The complete column scope retains the exact original duration sum. -/
lemma gf2MaterializePivotColumn_depth (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (materializePivotColumn output column).Path) :
    (materializePivotColumn output column).depth duration path =
      ((pivotColumnTrace (model := model) width column).map duration).sum :=
  gf2PivotColumnBody_depth _ _ column duration path

private lemma pivotRowBody_resident (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (path : (pivotRowBody used rows mask pivot column).Path) :
    (pivotRowBody used rows mask pivot column).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_seq, Circuit.peakResidentSpace_classical,
    Circuit.peakResidentSpace_classical]
  exact SpacePool.max_le (Word.PowerOfTwo.into_resident_le _ mask path.1)
    (SpacePool.max_le le_rfl le_rfl)

private lemma pivotColumnBody_resident (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (pivotColumnBody output mask column).Path) :
    (pivotColumnBody output mask column).peakResidentSpace path ≤ ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_seq
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask)) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakResidentSpace_classical]
  exact SpacePool.max_le (Word.PowerOfTwo.into_resident_le _ mask path.1) le_rfl

/-- The real row-mask scope adds only one row word to all original resident storage. -/
lemma gf2MaterializePivotRow_resident_le (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (materializePivotRow used rows pivot column).Path) :
    (materializePivotRow used rows pivot column).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord rowCount) + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh (placedPivotRow used rows pivot column) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _)
    (pivotRowBody_resident _ _ _ pivot column path)

/-- The separate column-mask scope adds one column word to the full resident context. -/
lemma gf2MaterializePivotColumn_resident_le (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (materializePivotColumn output column).Path) :
    (materializePivotColumn output column).peakResidentSpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.residentSpace := by
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (placedPivotColumn output column) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _)
    (pivotColumnBody_resident _ _ column path)

private lemma pivotRowBody_auxiliary (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (mask : CWriteRef ctx (.unsignedWord rowCount)) (pivot : Fin rowCount)
    (column : Fin width) (path : (pivotRowBody used rows mask pivot column).Path) :
    (pivotRowBody used rows mask pivot column).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Word.PowerOfTwo.into (model := model) (rowCount - 1 - pivot.val) mask)
    (.seq (BitWord.instruction (execution := model) (pivotOrOp used mask))
      (BitWord.instruction (execution := model)
        (pivotRowWriteOp rows mask column))) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_seq, Circuit.peakAuxiliarySpace_classical,
    Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_le (Word.PowerOfTwo.into_auxiliary_le _ mask path.1)
    (SpacePool.max_le le_rfl le_rfl)

private lemma pivotColumnBody_auxiliary (output mask : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (pivotColumnBody output mask column).Path) :
    (pivotColumnBody output mask column).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq
    (Word.PowerOfTwo.into (model := model) (width - 1 - column.val) mask)
    (BitWord.instruction (execution := model) (pivotOrOp output mask)) path).le.trans ?_
  unfold BitWord.instruction
  rw [Circuit.peakAuxiliarySpace_classical]
  exact SpacePool.max_le (Word.PowerOfTwo.into_auxiliary_le _ mask path.1) le_rfl

/-- The real row-mask scope adds only one row word to all original auxiliary storage. -/
lemma gf2MaterializePivotRow_auxiliary_le (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (pivot : Fin rowCount) (column : Fin width)
    (path : (materializePivotRow used rows pivot column).Path) :
    (materializePivotRow used rows pivot column).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord rowCount) + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord rowCount)
    ctx.canonicalFreshKey_fresh (placedPivotRow used rows pivot column) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _)
    (pivotRowBody_auxiliary _ _ _ pivot column path)

/-- The separate column-mask scope adds one column word to the full auxiliary context. -/
lemma gf2MaterializePivotColumn_auxiliary_le (output : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (path : (materializePivotColumn output column).Path) :
    (materializePivotColumn output column).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.unsignedWord width) + ctx.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (placedPivotColumn output column) path).le.trans ?_
  exact SpacePool.max_le (fun _axis => Nat.le_add_left _ _)
    (pivotColumnBody_auxiliary _ _ column path)

end QuantumAlg.ClassicalRoutines.GF2.Native
