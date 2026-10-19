/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Candidate
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Materialize.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Actual resources of pivot-record candidate construction

Every native allowance comes from the actual mask, comparison and original
column materializer. The free-mask copy and both ordered traversals remain
charged. Durations follow the same actual branch path as emitted events.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The selected coordinate of a candidate-construction operation. -/
def candidateOperationEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

/-- The actual coefficient test chooses the original one-hot/OR events or no events. -/
def candidateCoefficientEvents (width : Nat) (column : Fin width) :
    CShape.Value .bit → List (Resource.Event model)
  | .bit false => pivotColumnTrace (model := model) width column
  | .bit true => []

/-- Every possible row contribution retains its original native event coordinates. -/
def candidateRowEnvelope (width : Nat) (column : Fin width) :
    ResourcePool model :=
  ResourcePool.singleton (candidateOperationEvent (model := model) (.wordBinary .bitAnd width)) +
    (ResourcePool.singleton (candidateOperationEvent (model := model) (.wordBinary .equal width)) +
      ResourcePool.ofList (pivotColumnTrace (model := model) width column))

/-- The actual free-mask copy precedes both original nested traversal allowances. -/
def candidateEnvelope (rowCount width : Nat) : ResourcePool model :=
  ResourcePool.singleton (candidateOperationEvent (model := model) (.wordUnary .copy width)) +
    ∑ column : Fin width, ∑ _row : Fin rowCount, candidateRowEnvelope (model := model) width column

/-- A selected row preserves the original mask, equality and column-loader durations. -/
def candidateRowDepthLimit (width : Nat) (column : Fin width)
    (duration : Resource.Event model → Nat) : Nat :=
  duration (candidateOperationEvent (model := model) (.wordBinary .bitAnd width)) +
    (duration (candidateOperationEvent (model := model) (.wordBinary .equal width)) +
      ((pivotColumnTrace (model := model) width column).map duration).sum)

/-- The actual free-mask copy precedes every column and every row duration allowance. -/
def candidateDepthLimit (rowCount width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (candidateOperationEvent (model := model) (.wordUnary .copy width)) +
    ∑ column : Fin width, ∑ _row : Fin rowCount, candidateRowDepthLimit width column duration

private lemma coefficient_events (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit)
    (path : (candidateCoefficientChoice candidate column value).Path) :
    (candidateCoefficientChoice candidate column value).eventTrace path =
      candidateCoefficientEvents (model := model) width column value := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_events candidate column path
      · rfl

private lemma coefficient_duration (candidate : CWriteRef ctx (.unsignedWord width))
    (column : Fin width) (value : CShape.Value .bit) (duration : Resource.Event model → Nat)
    (path : (candidateCoefficientChoice candidate column value).Path) :
    (candidateCoefficientChoice candidate column value).depth duration path =
      ((candidateCoefficientEvents (model := model) width column value).map duration).sum := by
  cases value with
  | bit value =>
      cases value
      · exact gf2MaterializePivotColumn_depth candidate column duration path
      · rfl

/-- Both real unconditional operations precede exactly the selected coefficient events. -/
lemma gf2CandidateRowBody_events
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).eventTrace path =
      [candidateOperationEvent (model := model) (.wordBinary .bitAnd width),
        candidateOperationEvent (model := model) (.wordBinary .equal width)] ++
          candidateCoefficientEvents (model := model) width column path.2.2.1 := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (candidateMaskOp matrix free work row))
    (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag))
      (Circuit.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)))).Path at path
  change (BitWord.instruction (execution := model)
      (candidateMaskOp matrix free work row)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag)).eventTrace path.2.1 ++
      (candidateCoefficientChoice candidate column path.2.2.1).eventTrace path.2.2.2) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  exact congrArg (fun events : List (Resource.Event model) =>
    [candidateOperationEvent (model := model) (.wordBinary .bitAnd width),
      candidateOperationEvent (model := model) (.wordBinary .equal width)] ++ events)
    (coefficient_events candidate column path.2.2.1 path.2.2.2)

/-- The selected-row body has the exact duration sum of its actual emitted event trace. -/
lemma gf2CandidateRowBody_duration_eventTrace
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).depth duration path =
      (((candidateRowBody matrix free candidate zero work flag row column).eventTrace path).map
        duration).sum := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (candidateMaskOp matrix free work row))
    (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag))
      (Circuit.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)))).Path at path
  change (BitWord.instruction (execution := model)
      (candidateMaskOp matrix free work row)).depth duration path.1 +
    ((BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag)).depth duration path.2.1 +
      (candidateCoefficientChoice candidate column path.2.2.1).depth
        duration path.2.2.2) =
    (((BitWord.instruction (execution := model)
        (candidateMaskOp matrix free work row)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model)
          (decisionEqualityOp work zero flag)).eventTrace path.2.1 ++
        (candidateCoefficientChoice candidate column path.2.2.1).eventTrace
          path.2.2.2)).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change duration (candidateOperationEvent (model := model) (.wordBinary .bitAnd width)) +
    (duration (candidateOperationEvent (model := model) (.wordBinary .equal width)) +
      (candidateCoefficientChoice candidate column path.2.2.1).depth duration path.2.2.2) =
    (([candidateOperationEvent (model := model) (.wordBinary .bitAnd width),
      candidateOperationEvent (model := model) (.wordBinary .equal width)] ++
      (candidateCoefficientChoice candidate column path.2.2.1).eventTrace
        path.2.2.2).map duration).sum
  rw [coefficient_duration, coefficient_events]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc]

private lemma rowBody_pool_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).resourcePool path ≤
      candidateRowEnvelope (model := model) width column := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (candidateMaskOp matrix free work row))
    (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag))
      (Circuit.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model)
        (candidateMaskOp matrix free work row)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model)
          (decisionEqualityOp work zero flag)).eventTrace path.2.1 ++
        (candidateCoefficientChoice candidate column path.2.2.1).eventTrace
          path.2.2.2)) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList
    ([candidateOperationEvent (model := model) (.wordBinary .bitAnd width)] ++
      (([candidateOperationEvent (model := model) (.wordBinary .equal width)] :
          List (Resource.Event model)) ++
        (candidateCoefficientChoice candidate column path.2.2.1).eventTrace path.2.2.2)) ≤ _
  rw [coefficient_events]
  simp only [ResourcePool.ofList_append]
  refine add_le_add le_rfl (add_le_add le_rfl ?_)
  rcases path.2.2 with ⟨value, _path⟩
  cases value with
  | bit value =>
      cases value
      · exact le_rfl
      · change (0 : ResourcePool model) ≤ _
        exact zero_le

private lemma rowBody_depth_le
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (free candidate zero work : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (candidateRowBody matrix free candidate zero work flag row column).Path) :
    (candidateRowBody matrix free candidate zero work flag row column).depth duration path ≤
      candidateRowDepthLimit width column duration := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (candidateMaskOp matrix free work row))
    (Circuit.seq (BitWord.instruction (execution := model)
      (decisionEqualityOp work zero flag))
      (Circuit.branch (.storage flag.toCStorageRef)
        (candidateCoefficientChoice (model := model) candidate column)))).Path at path
  change (BitWord.instruction (execution := model)
      (candidateMaskOp matrix free work row)).depth duration path.1 +
    ((BitWord.instruction (execution := model)
        (decisionEqualityOp work zero flag)).depth duration path.2.1 +
      (candidateCoefficientChoice candidate column path.2.2.1).depth
        duration path.2.2.2) ≤ _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  change duration (candidateOperationEvent (model := model) (.wordBinary .bitAnd width)) +
    (duration (candidateOperationEvent (model := model) (.wordBinary .equal width)) +
      (candidateCoefficientChoice candidate column path.2.2.1).depth duration path.2.2.2) ≤ _
  rw [coefficient_duration]
  refine Nat.add_le_add_left (Nat.add_le_add_left ?_ _) _
  rcases path.2.2 with ⟨value, _path⟩
  cases value with
  | bit value =>
      cases value
      · exact le_rfl
      · exact Nat.zero_le _

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (free candidate zero : CWriteRef ctx (.unsignedWord width))

/-- The actual pivot bit selects a real row contribution within its original native allowance. -/
lemma gf2CandidatePivotRow_pool_le (row : Fin rowCount) (column : Fin width)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).resourcePool path ≤
      candidateRowEnvelope (model := model) width column := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (0 : ResourcePool model) ≤ _
        exact zero_le
      · exact rowBody_pool_le _ _ _ _ _ _ row column path

/-- Both outer scopes preserve the original duration allowance selected by the actual pivot bit. -/
lemma gf2CandidatePivotRow_depth_le (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).depth duration path ≤
      candidateRowDepthLimit width column duration := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact rowBody_depth_le _ _ _ _ _ _ row column duration path

/-- Every pivot-record branch preserves the exact serial sum of its actual emitted events. -/
lemma gf2CandidatePivotRow_duration_eventTrace (row : Fin rowCount) (column : Fin width)
    (duration : Resource.Event model → Nat)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).depth duration path =
      (((candidatePivotRow matrix rows free candidate zero row column).eventTrace path).map
        duration).sum := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact gf2CandidateRowBody_duration_eventTrace _ _ _ _ _ _ row column duration path

/-- The actual free-mask copy and every original column-major invocation remain charged. -/
lemma gf2BuildCandidate_pool_le (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).resourcePool path ≤
      candidateEnvelope (model := model) rowCount width := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow (model := model)
        matrix rows free candidate zero row column)))).Path at path
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model)
        (candidateCopyOp free candidate)).eventTrace path.1 ++
      (Circuit.forRange width (fun column => Circuit.forRange rowCount
        (fun row => candidatePivotRow matrix rows free candidate zero row column))).eventTrace
          path.2) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace]
  change ResourcePool.ofList ([candidateOperationEvent (model := model) (.wordUnary .copy width)] ++
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))).eventTrace
        path.2) ≤ _
  rw [ResourcePool.ofList_append]
  refine add_le_add le_rfl (Circuit.forRange_pool_le_sum width _ _ ?_ path.2)
  intro column current
  exact Circuit.forRange_pool_le_sum rowCount _ _
    (fun row => gf2CandidatePivotRow_pool_le matrix rows free candidate zero row column) current

/-- Both original nested loops retain each column's actual one-hot-loader duration allowance. -/
lemma gf2BuildCandidate_depth_le (duration : Resource.Event model → Nat)
    (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).depth duration path ≤
      candidateDepthLimit rowCount width duration := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow (model := model)
        matrix rows free candidate zero row column)))).Path at path
  change (BitWord.instruction (execution := model)
      (candidateCopyOp free candidate)).depth duration path.1 +
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))).depth
        duration path.2 ≤ _
  rw [BitWord.bitWord_instruction_depth]
  change duration (candidateOperationEvent (model := model) (.wordUnary .copy width)) +
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))).depth
        duration path.2 ≤ _
  refine Nat.add_le_add_left (Circuit.forRange_depth_le_sum width _ duration _ ?_ path.2) _
  intro column current
  exact Circuit.forRange_depth_le_sum rowCount _ duration _
    (fun row => gf2CandidatePivotRow_depth_le matrix rows free candidate zero row column duration)
    current

/-- The complete candidate construction retains exact same-path serial event durations. -/
lemma gf2BuildCandidate_duration_eventTrace (duration : Resource.Event model → Nat)
    (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).depth duration path =
      (((buildCandidate matrix rows free candidate zero).eventTrace path).map duration).sum := by
  change (Circuit.seq (BitWord.instruction (execution := model)
      (candidateCopyOp free candidate))
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow (model := model)
        matrix rows free candidate zero row column)))).Path at path
  change (BitWord.instruction (execution := model)
      (candidateCopyOp free candidate)).depth duration path.1 +
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))).depth
        duration path.2 =
    (((BitWord.instruction (execution := model)
        (candidateCopyOp free candidate)).eventTrace path.1 ++
      (Circuit.forRange width (fun column => Circuit.forRange rowCount
        (fun row => candidatePivotRow matrix rows free candidate zero row column))).eventTrace
          path.2).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
  change duration (candidateOperationEvent (model := model) (.wordUnary .copy width)) +
    (Circuit.forRange width (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column))).depth duration
        path.2 = _
  have serial := Circuit.forRange_duration_eventTrace width
    (fun column => Circuit.forRange rowCount
      (fun row => candidatePivotRow matrix rows free candidate zero row column)) duration
    (fun column => Circuit.forRange_duration_eventTrace rowCount _ duration
      (fun row => gf2CandidatePivotRow_duration_eventTrace matrix rows free candidate zero
        row column duration)) path.2
  rw [serial]
  change duration (candidateOperationEvent (model := model) (.wordUnary .copy width)) + _ =
    ((([candidateOperationEvent (model := model) (.wordUnary .copy width)] :
        List (Resource.Event model)) ++
      (Circuit.forRange width (fun column => Circuit.forRange rowCount
        (fun row => candidatePivotRow matrix rows free candidate zero row column))).eventTrace
          path.2).map duration).sum
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- A column can charge only its original fixed-width mask, comparison and one-hot instructions. -/
lemma gf2CandidatePivotRow_unit_depth_le (row : Fin rowCount) (column : Fin width)
    (path : (candidatePivotRow matrix rows free candidate zero row column).Path) :
    (candidatePivotRow matrix rows free candidate zero row column).depth (fun _ => 1) path ≤
      width + 4 := by
  refine (gf2CandidatePivotRow_depth_le matrix rows free candidate zero row column
    (fun _ => 1) path).trans ?_
  simp [candidateRowDepthLimit, pivotColumnTrace, Word.PowerOfTwo.powerTrace,
    Word.PowerOfTwo.shiftTrace]
  omega

/-- A safe all-path count retains the initial copy even when either traversal is empty. -/
lemma gf2BuildCandidate_unit_depth_le
    (path : (buildCandidate matrix rows free candidate zero).Path) :
    (buildCandidate matrix rows free candidate zero).depth (fun _ => 1) path ≤
      1 + width * (rowCount * (width + 4)) := by
  refine Nat.add_le_add_left (Circuit.forRange_depth_le width _ _ ?_ path.2) 1
  intro column current
  exact Circuit.forRange_depth_le rowCount _ _
    (fun row => gf2CandidatePivotRow_unit_depth_le matrix rows free candidate zero row column)
    current

end

end QuantumAlg.ClassicalRoutines.GF2.Native
