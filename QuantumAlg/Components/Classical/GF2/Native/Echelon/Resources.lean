/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Echelon
import all QuantumAlg.Components.Classical.GF2.Native.Load.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Pivot.Resources

/-!
# Native resources of the complete matrix-reduction prefix

All original initialization instructions and every actual column invocation
remain charged. The row-zero source comes from its real lexical allocation;
no extra self-XOR is inserted. Column allowances retain the explicit
all-syntactic-path boundary of the existing pivot resource theorems.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The selected coordinate of a matrix-reduction initialization. -/
def echelonOperationEvent (label : Resource.ClassicalOpLabel) : Resource.Event model :=
  .classicalOperation (BitWord.selectedCoordinate (execution := model) label)

/-- The original vector-write event used by every pivot-row initialization entry. -/
def pivotRowsClearEvent (rowCount width : Nat) : Resource.Event model :=
  echelonOperationEvent (model := model) (.vector .write width rowCount)

omit [BitWord.Selected model] in
private theorem repeated_trace (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (event : Resource.Event model)
    (events : ∀ index path, (body index).eventTrace path = [event])
    (path : (Circuit.forRange count body).Path) :
    (Circuit.forRange count body).eventTrace path = List.replicate count event := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (body 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2 = _
      rw [events, ih _ (fun index => events index.succ), List.replicate_succ]
      rfl

/-- Every initialization path contains exactly the original ordered vector writes. -/
theorem gf2PivotRowsClearBody_events
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount))
    (path : (pivotRowsClearBody rows zero).Path) :
    (pivotRowsClearBody rows zero).eventTrace path =
      List.replicate width (pivotRowsClearEvent (model := model) rowCount width) :=
  repeated_trace width _ _ (fun column current => by
    rw [BitWord.bitWord_instruction_eventTrace]
    change [pivotRowsClearEvent (model := model) rowCount width] = _
    rfl) path

/-- The same actual initialization path has exact serial event-duration accounting. -/
theorem gf2PivotRowsClearBody_duration_eventTrace
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (zero : CWriteRef ctx (.unsignedWord rowCount)) (duration : Resource.Event model → Nat)
    (path : (pivotRowsClearBody rows zero).Path) :
    (pivotRowsClearBody rows zero).depth duration path =
      (((pivotRowsClearBody rows zero).eventTrace path).map duration).sum :=
  Circuit.forRange_duration_eventTrace width _ duration
    (fun column current => by
      rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_eventTrace]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]) path

/-- Real lexical entry and exit add no events to the original initialization writes. -/
theorem gf2ClearPivotRows_events
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (path : (clearPivotRows rows).Path) :
    (clearPivotRows rows).eventTrace path =
      List.replicate width (pivotRowsClearEvent (model := model) rowCount width) :=
  gf2PivotRowsClearBody_events _ _ path

/-- The complete initialization scope charges every vector-write duration exactly once. -/
theorem gf2ClearPivotRows_depth
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (duration : Resource.Event model → Nat) (path : (clearPivotRows rows).Path) :
    (clearPivotRows rows).depth duration path =
      width * duration (pivotRowsClearEvent (model := model) rowCount width) := by
  have serial := gf2PivotRowsClearBody_duration_eventTrace
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) duration path
  have trace := gf2PivotRowsClearBody_events
    (rows.underWorkspace ctx.canonicalFreshKey (.unsignedWord rowCount)
      ctx.canonicalFreshKey_fresh) (pivotMaskCell ctx rowCount) path
  have complete := serial.trans (congrArg
    (fun events : List (Resource.Event model) => (events.map duration).sum) trace)
  exact complete.trans (by
    simp only [List.map_replicate, List.sum_replicate, smul_eq_mul])

/-- All original initialization event coordinates precede the individual column allowances. -/
def echelonEnvelope (rowCount width : Nat) : ResourcePool model :=
  ResourcePool.singleton (echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)) +
    (ResourcePool.singleton (echelonOperationEvent (model := model) (.wordBinary .bitXor width)) +
      (ResourcePool.scale width
          (ResourcePool.singleton (pivotRowsClearEvent (model := model) rowCount width)) +
        ∑ column, pivotColumnEnvelope (model := model) rowCount width column))

/-- The original three initialization stages precede every column's duration allowance. -/
def echelonDepthLimit (rowCount width : Nat) (duration : Resource.Event model → Nat) : Nat :=
  duration (echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)) +
    (duration (echelonOperationEvent (model := model) (.wordBinary .bitXor width)) +
      (width * duration (pivotRowsClearEvent (model := model) rowCount width) +
        ∑ column, pivotColumnDepthLimit rowCount width column duration))

variable (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns : CWriteRef ctx (.unsignedWord width))

/-- Complete reduction charges both real self-XORs, all initialization writes and all columns. -/
theorem gf2ReduceMatrix_pool_le (path : (reduceMatrix matrix used rows columns).Path) :
    (reduceMatrix matrix used rows columns).resourcePool path ≤
      echelonEnvelope (model := model) rowCount width := by
    change (Circuit.seq
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
      (Circuit.seq
        (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
        (Circuit.seq (clearPivotRows (model := model) rows)
          (Circuit.forRange width
            (reduceColumn (model := model) matrix used rows columns))))).Path at path
    change ResourcePool.ofList
      ((BitWord.instruction (execution := model)
          (Word.PowerOfTwo.clearOp used)).eventTrace path.1 ++
        ((BitWord.instruction (execution := model)
            (Word.PowerOfTwo.clearOp columns)).eventTrace path.2.1 ++
          ((clearPivotRows rows).eventTrace path.2.2.1 ++
            (Circuit.forRange width (reduceColumn matrix used rows columns)).eventTrace
              path.2.2.2))) ≤ _
    rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
    change ResourcePool.ofList
      ([echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)] ++
        ([echelonOperationEvent (model := model) (.wordBinary .bitXor width)] ++
          ((clearPivotRows rows).eventTrace path.2.2.1 ++
            (Circuit.forRange width (reduceColumn matrix used rows columns)).eventTrace
              path.2.2.2))) ≤ _
    rw [gf2ClearPivotRows_events]
    simp only [ResourcePool.ofList_append, ResourcePool.ofList_replicate]
    exact add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
      (Circuit.forRange_pool_le_sum width _ _
        (gf2ReduceColumn_pool_le matrix used rows columns) path.2.2.2)))

/-- The original serial initialization precedes each column's actual duration allowance. -/
theorem gf2ReduceMatrix_depth_le (duration : Resource.Event model → Nat)
    (path : (reduceMatrix matrix used rows columns).Path) :
    (reduceMatrix matrix used rows columns).depth duration path ≤
      echelonDepthLimit rowCount width duration := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
    (Circuit.seq
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (Circuit.seq (clearPivotRows (model := model) rows)
        (Circuit.forRange width
          (reduceColumn (model := model) matrix used rows columns))))).Path at path
  change (BitWord.instruction (execution := model)
      (Word.PowerOfTwo.clearOp used)).depth duration path.1 +
    ((BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp columns)).depth duration path.2.1 +
      ((clearPivotRows rows).depth duration path.2.2.1 +
        (Circuit.forRange width (reduceColumn matrix used rows columns)).depth duration
          path.2.2.2)) ≤ _
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth]
  change duration (echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)) +
    (duration (echelonOperationEvent (model := model) (.wordBinary .bitXor width)) +
      ((clearPivotRows rows).depth duration path.2.2.1 +
        (Circuit.forRange width (reduceColumn matrix used rows columns)).depth duration
          path.2.2.2)) ≤ _
  rw [gf2ClearPivotRows_depth]
  exact Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add_left
    (Circuit.forRange_depth_le_sum width _ duration _
      (fun column => gf2ReduceColumn_depth_le matrix used rows columns column duration)
      path.2.2.2) _) _) _

/-- Every complete reduction path retains its exact emitted serial-duration sum. -/
theorem gf2ReduceMatrix_duration_eventTrace (duration : Resource.Event model → Nat)
    (path : (reduceMatrix matrix used rows columns).Path) :
    (reduceMatrix matrix used rows columns).depth duration path =
      (((reduceMatrix matrix used rows columns).eventTrace path).map duration).sum := by
  change (Circuit.seq
    (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp used))
    (Circuit.seq
      (BitWord.instruction (execution := model) (Word.PowerOfTwo.clearOp columns))
      (Circuit.seq (clearPivotRows (model := model) rows)
        (Circuit.forRange width
          (reduceColumn (model := model) matrix used rows columns))))).Path at path
  change (BitWord.instruction (execution := model)
      (Word.PowerOfTwo.clearOp used)).depth duration path.1 +
    ((BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp columns)).depth duration path.2.1 +
      ((clearPivotRows rows).depth duration path.2.2.1 +
        (Circuit.forRange width (reduceColumn matrix used rows columns)).depth duration
          path.2.2.2)) =
    (((BitWord.instruction (execution := model)
        (Word.PowerOfTwo.clearOp used)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model)
          (Word.PowerOfTwo.clearOp columns)).eventTrace path.2.1 ++
        ((clearPivotRows rows).eventTrace path.2.2.1 ++
          (Circuit.forRange width (reduceColumn matrix used rows columns)).eventTrace
            path.2.2.2))).map duration).sum
  rw [BitWord.bitWord_instruction_depth, BitWord.bitWord_instruction_depth,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  change duration (echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)) +
    (duration (echelonOperationEvent (model := model) (.wordBinary .bitXor width)) +
      ((clearPivotRows rows).depth duration path.2.2.1 +
        (Circuit.forRange width (reduceColumn matrix used rows columns)).depth duration
          path.2.2.2)) =
    ((([echelonOperationEvent (model := model) (.wordBinary .bitXor rowCount)] :
        List (Resource.Event model)) ++
      (([echelonOperationEvent (model := model) (.wordBinary .bitXor width)] :
          List (Resource.Event model)) ++
        ((clearPivotRows rows).eventTrace path.2.2.1 ++
          (Circuit.forRange width (reduceColumn matrix used rows columns)).eventTrace
            path.2.2.2))).map duration).sum
  rw [gf2ClearPivotRows_depth, gf2ClearPivotRows_events,
    Circuit.forRange_duration_eventTrace width _ duration
      (fun column => gf2ReduceColumn_duration_eventTrace matrix used rows columns column duration)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_replicate, List.sum_replicate, smul_eq_mul, Nat.add_zero]

/-- The actual loading and reduction prefix adds both original native resource allowances. -/
theorem gf2LoadAndReduce_pool_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (path : (loadAndReduce input matrix used rows columns).Path) :
    (loadAndReduce input matrix used rows columns).resourcePool path ≤
      ResourcePool.scale rowCount (rowEnvelope (model := model) rowCount width) +
        echelonEnvelope (model := model) rowCount width := by
  change ResourcePool.ofList ((loadMatrix input matrix).eventTrace path.1 ++
    (reduceMatrix matrix used rows columns).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (gf2LoadMatrix_pool_le input matrix path.1)
    (gf2ReduceMatrix_pool_le matrix used rows columns path.2)

/-- The complete original loading duration is followed by the initialized reduction duration. -/
theorem gf2LoadAndReduce_depth_le (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (duration : Resource.Event model → Nat)
    (path : (loadAndReduce input matrix used rows columns).Path) :
    (loadAndReduce input matrix used rows columns).depth duration path ≤
      rowCount * rowDepthLimit rowCount width duration +
        echelonDepthLimit rowCount width duration :=
  Nat.add_le_add (gf2LoadMatrix_depth_le input matrix duration path.1)
    (gf2ReduceMatrix_depth_le matrix used rows columns duration path.2)

/-- Both real prefix phases retain the exact duration sum of their original emitted events. -/
theorem gf2LoadAndReduce_duration_eventTrace
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (duration : Resource.Event model → Nat)
    (path : (loadAndReduce input matrix used rows columns).Path) :
    (loadAndReduce input matrix used rows columns).depth duration path =
      (((loadAndReduce input matrix used rows columns).eventTrace path).map duration).sum := by
  change (loadMatrix input matrix).depth duration path.1 +
    (reduceMatrix matrix used rows columns).depth duration path.2 =
      (((loadMatrix input matrix).eventTrace path.1 ++
        (reduceMatrix matrix used rows columns).eventTrace path.2).map duration).sum
  rw [List.map_append, List.sum_append]
  exact congrArg₂ (· + ·) (gf2LoadMatrix_duration_eventTrace input matrix duration path.1)
    (gf2ReduceMatrix_duration_eventTrace matrix used rows columns duration path.2)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
