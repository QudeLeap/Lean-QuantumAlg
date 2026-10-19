/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Eliminate.Resources

/-!
# Native resources of the actual ordered pivot search

Actual paths retain every original marker, loader, record write and row-XOR.
The independent bounds below apply even to syntactic paths whose stored-bit
choices are not jointly reachable. They therefore allow a selected arm at
each row, without claiming a tight bound for the actual first-pivot record.
The two outer bits are allocated once per column; mask-word space is a maximum.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The selected coordinate of a pivot-search operation. -/
def pivotOperationEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

private lemma pivotInstruction_duration_eventTrace {input output : CShape}
    (op : ClassicalOp input output ctx ctx) (duration : Resource.Event model → Nat)
    (path : (BitWord.instruction (execution := model) op).Path) :
    (BitWord.instruction (execution := model) op).depth duration path =
      ((((BitWord.instruction (execution := model) op).eventTrace path).map duration).sum) := by
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The original five-stage selected-pivot native allowance. -/
def selectedPivotEnvelope (rowCount width : Nat)
    (row : Fin rowCount) (column : Fin width) : ResourcePool model :=
  ResourcePool.singleton (pivotOperationEvent (model := model) (.bit .and)) +
    (ResourcePool.singleton (pivotOperationEvent (model := model) (.bit .not)) +
      (ResourcePool.ofList (pivotRowTrace (model := model) rowCount width row) +
        (ResourcePool.ofList (pivotColumnTrace (model := model) width column) +
          ResourcePool.scale rowCount
            (ResourcePool.singleton (eliminationEvent (model := model) rowCount width)))))

/-- Rejection and selection preserve distinct original native event coordinates. -/
def pivotProbeEnvelope (rowCount width : Nat)
    (row : Fin rowCount) (column : Fin width) : ResourcePool model :=
  ResourcePool.max (ResourcePool.singleton (pivotOperationEvent (model := model) (.bit .copy)))
    (selectedPivotEnvelope (model := model) rowCount width row column)

/-- All-path column allowance: original found clear, each row arm and final no-pivot marker. -/
def pivotColumnEnvelope (rowCount width : Nat) (column : Fin width) :
    ResourcePool model :=
  ResourcePool.singleton (pivotOperationEvent (model := model) (.bit .xor)) +
    ((∑ row, pivotProbeEnvelope (model := model) rowCount width row column) +
      ResourcePool.singleton (pivotOperationEvent (model := model) (.bit .xor)))

/-- Arbitrary-duration allowance preserves all five selected-pivot stages. -/
def selectedPivotDepthLimit (rowCount width : Nat) (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat) : Nat :=
  duration (pivotOperationEvent (model := model) (.bit .and)) +
    (duration (pivotOperationEvent (model := model) (.bit .not)) +
      (((pivotRowTrace (model := model) rowCount width row).map duration).sum +
        (((pivotColumnTrace (model := model) width column).map duration).sum +
          rowCount * duration (eliminationEvent (model := model) rowCount width))))

/-- Each row's duration allowance retains the actual rejection-or-selection alternative. -/
def pivotProbeDepthLimit (rowCount width : Nat) (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat) : Nat :=
  max (duration (pivotOperationEvent (model := model) (.bit .copy)))
    (selectedPivotDepthLimit rowCount width row column duration)

/-- The complete column adds the original clear and final no-pivot instruction allowances. -/
def pivotColumnDepthLimit (rowCount width : Nat) (column : Fin width)
    (duration : Resource.Event model → Nat) : Nat :=
  duration (pivotOperationEvent (model := model) (.bit .xor)) +
    ((∑ row, pivotProbeDepthLimit rowCount width row column duration) +
      duration (pivotOperationEvent (model := model) (.bit .xor)))

/-- The two mask words are sequential scopes, so their live-space allowance is a maximum. -/
def pivotMaskSpace (rowCount width : Nat) : SpacePool model.kind :=
  SpacePool.max (SpacePool.ofShape (.unsignedWord rowCount))
    (SpacePool.ofShape (.unsignedWord width))

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width)) (found sink : CWriteRef ctx .bit)

/-- Every actually emitted selected-pivot event retains its native coordinate. -/
lemma gf2SelectPivot_pool_le (row : Fin rowCount) (column : Fin width)
    (path : (selectPivot matrix used rows columns found sink row column).Path) :
    (selectPivot matrix used rows columns found sink row column).resourcePool path ≤
      selectedPivotEnvelope (model := model) rowCount width row column := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (Circuit.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (Circuit.seq (materializePivotRow (model := model) used rows row column)
        (Circuit.seq (materializePivotColumn (model := model) columns column)
          (eliminateWithPivot (model := model) matrix row column))))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (pivotSelectedOp sink)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model) (pivotFoundOp found)).eventTrace path.2.1 ++
        ((materializePivotRow used rows row column).eventTrace path.2.2.1 ++
          ((materializePivotColumn columns column).eventTrace path.2.2.2.1 ++
            (eliminateWithPivot matrix row column).eventTrace path.2.2.2.2)))) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList
    ([pivotOperationEvent (model := model) (.bit .and)] ++
      (([pivotOperationEvent (model := model) (.bit .not)] : List (Resource.Event model)) ++
      ((materializePivotRow used rows row column).eventTrace path.2.2.1 ++
        ((materializePivotColumn columns column).eventTrace path.2.2.2.1 ++
          (eliminateWithPivot matrix row column).eventTrace path.2.2.2.2)))) ≤ _
  rw [gf2MaterializePivotRow_events, gf2MaterializePivotColumn_events]
  simp only [ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (gf2EliminateWithPivot_pool_le matrix row column path.2.2.2.2))))

/-- Arbitrary selected-pivot durations add the same five actual stages. -/
lemma gf2SelectPivot_depth_le (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (selectPivot matrix used rows columns found sink row column).Path) :
    (selectPivot matrix used rows columns found sink row column).depth duration path ≤
      selectedPivotDepthLimit rowCount width row column duration := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (Circuit.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (Circuit.seq (materializePivotRow (model := model) used rows row column)
        (Circuit.seq (materializePivotColumn (model := model) columns column)
          (eliminateWithPivot (model := model) matrix row column))))).Path at path
  change (BitWord.instruction (execution := model) (pivotSelectedOp sink)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (pivotFoundOp found)).depth duration path.2.1 +
      ((materializePivotRow used rows row column).depth duration path.2.2.1 +
        ((materializePivotColumn columns column).depth duration path.2.2.2.1 +
          (eliminateWithPivot matrix row column).depth duration path.2.2.2.2))) ≤ _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  change duration (pivotOperationEvent (model := model) (.bit .and)) +
    (duration (pivotOperationEvent (model := model) (.bit .not)) +
      ((materializePivotRow used rows row column).depth duration path.2.2.1 +
        ((materializePivotColumn columns column).depth duration path.2.2.2.1 +
          (eliminateWithPivot matrix row column).depth duration path.2.2.2.2))) ≤ _
  rw [gf2MaterializePivotRow_depth, gf2MaterializePivotColumn_depth]
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (Nat.add_le_add_left (gf2EliminateWithPivot_depth_le matrix row column duration
      path.2.2.2.2) _) _) _) _

/-- Selected-pivot depth is exactly the sum of the durations of its actual emitted events. -/
lemma gf2SelectPivot_duration_eventTrace (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (selectPivot matrix used rows columns found sink row column).Path) :
    (selectPivot matrix used rows columns found sink row column).depth duration path =
      (((selectPivot matrix used rows columns found sink row column).eventTrace path).map
        duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotSelectedOp sink))
    (Circuit.seq (BitWord.instruction (execution := model) (pivotFoundOp found))
      (Circuit.seq (materializePivotRow (model := model) used rows row column)
        (Circuit.seq (materializePivotColumn (model := model) columns column)
          (eliminateWithPivot (model := model) matrix row column))))).Path at path
  change (BitWord.instruction (execution := model) (pivotSelectedOp sink)).depth
      duration path.1 +
    ((BitWord.instruction (execution := model) (pivotFoundOp found)).depth duration path.2.1 +
      ((materializePivotRow used rows row column).depth duration path.2.2.1 +
        ((materializePivotColumn columns column).depth duration path.2.2.2.1 +
          (eliminateWithPivot matrix row column).depth duration path.2.2.2.2))) =
    (((BitWord.instruction (execution := model) (pivotSelectedOp sink)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model) (pivotFoundOp found)).eventTrace path.2.1 ++
        ((materializePivotRow used rows row column).eventTrace path.2.2.1 ++
          ((materializePivotColumn columns column).eventTrace path.2.2.2.1 ++
            (eliminateWithPivot matrix row column).eventTrace path.2.2.2.2)))).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change duration (pivotOperationEvent (model := model) (.bit .and)) +
    (duration (pivotOperationEvent (model := model) (.bit .not)) +
      ((materializePivotRow used rows row column).depth duration path.2.2.1 +
        ((materializePivotColumn columns column).depth duration path.2.2.2.1 +
          (eliminateWithPivot matrix row column).depth duration path.2.2.2.2))) =
    ((([pivotOperationEvent (model := model) (.bit .and)] : List (Resource.Event model)) ++
      (([pivotOperationEvent (model := model) (.bit .not)] : List (Resource.Event model)) ++
      ((materializePivotRow used rows row column).eventTrace path.2.2.1 ++
        ((materializePivotColumn columns column).eventTrace path.2.2.2.1 ++
          (eliminateWithPivot matrix row column).eventTrace path.2.2.2.2)))).map duration).sum
  rw [gf2MaterializePivotRow_depth, gf2MaterializePivotColumn_depth,
    gf2EliminateWithPivot_duration_eventTrace, gf2MaterializePivotRow_events,
    gf2MaterializePivotColumn_events]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- All original branch choices respect the per-row native allowance. -/
lemma gf2PivotProbeRow_pool_le (row : Fin rowCount) (column : Fin width)
    (path : (pivotProbeRow matrix used rows columns found sink row column).Path) :
    (pivotProbeRow matrix used rows columns found sink row column).resourcePool path ≤
      pivotProbeEnvelope (model := model) rowCount width row column := by
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
      · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
        change ResourcePool.ofList
          ((BitWord.instruction (execution := model) (pivotRejectedOp sink)).eventTrace path) ≤ _
        rw [BitWord.bitWord_instruction_eventTrace]
        exact ResourcePool.le_max_left _ _
      · exact (gf2SelectPivot_pool_le matrix used rows columns found sink row column path).trans
          (ResourcePool.le_max_right _ _)
    · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
      change ResourcePool.ofList
        ((BitWord.instruction (execution := model) (pivotRejectedOp sink)).eventTrace path) ≤ _
      rw [BitWord.bitWord_instruction_eventTrace]
      exact ResourcePool.le_max_left _ _
  · change (0 : ResourcePool model) ≤ _
    exact zero_le

/-- The actual three branch choices respect each row's duration allowance. -/
lemma gf2PivotProbeRow_depth_le (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (pivotProbeRow matrix used rows columns found sink row column).Path) :
    (pivotProbeRow matrix used rows columns found sink row column).depth duration path ≤
      pivotProbeDepthLimit rowCount width row column duration := by
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
      · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
        change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).depth
          duration path ≤ _
        rw [BitWord.bitWord_instruction_depth]
        exact Nat.le_max_left _ _
      · exact (gf2SelectPivot_depth_le matrix used rows columns found sink row column duration
          path).trans (Nat.le_max_right _ _)
    · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
      change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).depth
        duration path ≤ _
      rw [BitWord.bitWord_instruction_depth]
      exact Nat.le_max_left _ _
  · exact Nat.zero_le _

/-- Each row path retains exact serial event-duration accounting. -/
lemma gf2PivotProbeRow_duration_eventTrace (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (pivotProbeRow matrix used rows columns found sink row column).Path) :
    (pivotProbeRow matrix used rows columns found sink row column).depth duration path =
      (((pivotProbeRow matrix used rows columns found sink row column).eventTrace path).map
        duration).sum := by
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
      · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
        change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).depth
          duration path =
            ((((BitWord.instruction (execution := model)
              (pivotRejectedOp sink)).eventTrace path).map duration).sum)
        exact pivotInstruction_duration_eventTrace (pivotRejectedOp sink) duration path
      · exact gf2SelectPivot_duration_eventTrace matrix used rows columns found sink row column
          duration path
    · change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).Path at path
      change (BitWord.instruction (execution := model) (pivotRejectedOp sink)).depth
        duration path =
          ((((BitWord.instruction (execution := model)
            (pivotRejectedOp sink)).eventTrace path).map duration).sum)
      exact pivotInstruction_duration_eventTrace (pivotRejectedOp sink) duration path
  · rfl

/-- The all-path native column allowance includes every real marker and every row arm. -/
lemma gf2ReduceColumnBody_pool_le (column : Fin width)
    (path : (reduceColumnBody matrix used rows columns found sink column).Path) :
    (reduceColumnBody matrix used rows columns found sink column).resourcePool path ≤
      pivotColumnEnvelope (model := model) rowCount width column := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotClearOp found))
    (Circuit.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model)
        matrix used rows columns found sink row column))
      (Circuit.branch (.storage found.toCStorageRef)
        (pivotAbsentChoice (model := model) sink)))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (pivotClearOp found)).eventTrace path.1 ++
      ((Circuit.forRange rowCount
        (fun row => pivotProbeRow matrix used rows columns found sink row column)).eventTrace
          path.2.1 ++
        (pivotAbsentChoice sink path.2.2.1).eventTrace path.2.2.2)) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList ([pivotOperationEvent (model := model) (.bit .xor)] ++
    ((Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column)).eventTrace path.2.1
        ++
      (pivotAbsentChoice sink path.2.2.1).eventTrace path.2.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  refine add_le_add le_rfl (add_le_add
    (Circuit.forRange_pool_le_sum rowCount _ _
      (fun row => gf2PivotProbeRow_pool_le matrix used rows columns found sink row column)
      path.2.1) ?_)
  rcases path.2.2 with ⟨value, last⟩
  cases value
  rename_i isFound
  cases isFound
  · change (BitWord.instruction (execution := model) (pivotClearOp sink)).Path at last
    change ResourcePool.ofList
      ((BitWord.instruction (execution := model) (pivotClearOp sink)).eventTrace last) ≤ _
    rw [BitWord.bitWord_instruction_eventTrace]
    change ResourcePool.ofList [pivotOperationEvent (model := model) (.bit .xor)] ≤ _
    exact le_rfl
  · change (0 : ResourcePool model) ≤ _
    exact zero_le

/-- Each row retains its own original duration allowance in the increasing sequence. -/
lemma gf2ReduceColumnBody_depth_le (column : Fin width) (duration : Resource.Event model → Nat)
    (path : (reduceColumnBody matrix used rows columns found sink column).Path) :
    (reduceColumnBody matrix used rows columns found sink column).depth duration path ≤
      pivotColumnDepthLimit rowCount width column duration := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotClearOp found))
    (Circuit.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model)
        matrix used rows columns found sink row column))
      (Circuit.branch (.storage found.toCStorageRef)
        (pivotAbsentChoice (model := model) sink)))).Path at path
  change (BitWord.instruction (execution := model) (pivotClearOp found)).depth
      duration path.1 +
    ((Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column)).depth duration
        path.2.1 + (pivotAbsentChoice sink path.2.2.1).depth duration path.2.2.2) ≤ _
  rw [BitWord.bitWord_instruction_depth]
  change duration (pivotOperationEvent (model := model) (.bit .xor)) +
    ((Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column)).depth duration
        path.2.1 + (pivotAbsentChoice sink path.2.2.1).depth duration path.2.2.2) ≤ _
  refine Nat.add_le_add_left (Nat.add_le_add
    (Circuit.forRange_depth_le_sum rowCount _ duration _
      (fun row => gf2PivotProbeRow_depth_le matrix used rows columns found sink row column duration)
      path.2.1) ?_) _
  rcases path.2.2 with ⟨value, last⟩
  cases value
  rename_i isFound
  cases isFound
  · change (BitWord.instruction (execution := model) (pivotClearOp sink)).Path at last
    change (BitWord.instruction (execution := model) (pivotClearOp sink)).depth
      duration last ≤ _
    rw [BitWord.bitWord_instruction_depth]
    change duration (pivotOperationEvent (model := model) (.bit .xor)) ≤ _
    exact le_rfl
  · exact Nat.zero_le _

/-- The complete actual column path has serial depth equal to its native duration sum. -/
lemma gf2ReduceColumnBody_duration_eventTrace (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (reduceColumnBody matrix used rows columns found sink column).Path) :
    (reduceColumnBody matrix used rows columns found sink column).depth duration path =
      (((reduceColumnBody matrix used rows columns found sink column).eventTrace path).map
        duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model) (pivotClearOp found))
    (Circuit.seq (Circuit.forRange rowCount
      (fun row => pivotProbeRow (model := model)
        matrix used rows columns found sink row column))
      (Circuit.branch (.storage found.toCStorageRef)
        (pivotAbsentChoice (model := model) sink)))).Path at path
  change (BitWord.instruction (execution := model) (pivotClearOp found)).depth
      duration path.1 +
    ((Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column)).depth duration
        path.2.1 + (pivotAbsentChoice sink path.2.2.1).depth duration path.2.2.2) =
    (((BitWord.instruction (execution := model) (pivotClearOp found)).eventTrace path.1 ++
      ((Circuit.forRange rowCount
        (fun row => pivotProbeRow matrix used rows columns found sink row column)).eventTrace
          path.2.1 ++ (pivotAbsentChoice sink path.2.2.1).eventTrace
            path.2.2.2)).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
  change duration (pivotOperationEvent (model := model) (.bit .xor)) +
    ((Circuit.forRange rowCount
      (fun row => pivotProbeRow matrix used rows columns found sink row column)).depth duration
        path.2.1 + (pivotAbsentChoice sink path.2.2.1).depth duration path.2.2.2) =
    ((([pivotOperationEvent (model := model) (.bit .xor)] : List (Resource.Event model)) ++
      ((Circuit.forRange rowCount
        (fun row => pivotProbeRow matrix used rows columns found sink row column)).eventTrace
          path.2.1 ++ (pivotAbsentChoice sink path.2.2.1).eventTrace path.2.2.2)).map duration).sum
  rw [Circuit.forRange_duration_eventTrace rowCount _ duration
    (fun row => gf2PivotProbeRow_duration_eventTrace matrix used rows columns found sink row column
      duration)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  congr 2
  rcases path.2.2 with ⟨value, last⟩
  cases value
  rename_i isFound
  cases isFound
  · change (BitWord.instruction (execution := model) (pivotClearOp sink)).Path at last
    change (BitWord.instruction (execution := model) (pivotClearOp sink)).depth
      duration last =
        ((((BitWord.instruction (execution := model)
          (pivotClearOp sink)).eventTrace last).map duration).sum)
    exact pivotInstruction_duration_eventTrace (pivotClearOp sink) duration last
  · rfl

/-- Both real bit scopes retain the original column's native allowance. -/
lemma gf2ReduceColumn_pool_le (column : Fin width)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).resourcePool path ≤
      pivotColumnEnvelope (model := model) rowCount width column :=
  gf2ReduceColumnBody_pool_le _ _ _ _ _ _ column path

/-- Both real bit scopes retain the original column's arbitrary-duration allowance. -/
lemma gf2ReduceColumn_depth_le (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).depth duration path ≤
      pivotColumnDepthLimit rowCount width column duration :=
  gf2ReduceColumnBody_depth_le _ _ _ _ _ _ column duration path

/-- Both real bit scopes preserve the exact actual serial-duration equation. -/
lemma gf2ReduceColumn_duration_eventTrace (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).depth duration path =
      (((reduceColumn matrix used rows columns column).eventTrace path).map duration).sum :=
  gf2ReduceColumnBody_duration_eventTrace _ _ _ _ _ _ column duration path

/-- A unit-duration allowance for all paths, with no reachability or zero-state promise. -/
lemma gf2ReduceColumn_unit_depth_le (column : Fin width)
    (path : (reduceColumn matrix used rows columns column).Path) :
    (reduceColumn matrix used rows columns column).depth (fun _ => 1) path ≤
      rowCount * (2 * rowCount + width + 9) + 2 := by
  have eachRow : ∀ row : Fin rowCount,
      pivotProbeDepthLimit rowCount width row column (fun _ : Resource.Event model => 1) ≤
        2 * rowCount + width + 9 := by
    intro row
    refine Nat.max_le.mpr ⟨by change 1 ≤ _; omega, ?_⟩
    simp only [selectedPivotDepthLimit, pivotRowTrace, pivotColumnTrace,
      Word.PowerOfTwo.powerTrace, Word.PowerOfTwo.shiftTrace, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.map_replicate, List.sum_replicate, smul_eq_mul, Nat.mul_one, Nat.add_zero]
    omega
  refine (gf2ReduceColumn_depth_le matrix used rows columns column (fun _ => 1) path).trans ?_
  have sumBound := Finset.sum_le_sum (fun row (_present : row ∈ Finset.univ) => eachRow row)
  simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at sumBound
  change 1 + ((∑ row, pivotProbeDepthLimit rowCount width row column
    (fun _ : Resource.Event model => 1)) + 1) ≤ _
  omega

end

end QuantumAlg.ClassicalRoutines.GF2.Native
