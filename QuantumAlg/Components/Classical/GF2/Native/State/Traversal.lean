/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State.Column.Scope

/-!
# Original increasing-column traversal of the actual seven GF(2) cells

The existing finite circuit record advances the real store at every column.
The original pure pivot-column avoidance invariant supplies each local absence
condition. No host-selected pivot, supplied execution result or new initial
state requirement is used. The original initialization is a separate stage.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem absent_of_avoid (state : ClassicalAlgorithms.GF2.State rowCount width)
    (column : Fin width) (remaining : List (Fin width))
    (avoid : ClassicalAlgorithms.GF2.PivotColumnsAvoid state (column :: remaining)) :
    state.pivots.find? (fun entry => decide (entry.column = column)) = none := by
  apply List.find?_eq_none.mpr
  intro pivot member selected
  have same : pivot.column = column := of_decide_eq_true selected
  have recorded : column ∈ ClassicalAlgorithms.GF2.pivotColumns state.pivots :=
    List.mem_map.mpr ⟨pivot, member, same⟩
  exact avoid recorded (List.mem_cons_self ..)

private theorem traverse (cells : Cells ctx (stateShapes rowCount width))
    (distinct : cells.Distinct) (count : Nat) (indices : Fin count → Fin width)
    (nodup : (List.ofFn indices).Nodup) (store : Store ctx)
    (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state)
    (avoid : ClassicalAlgorithms.GF2.PivotColumnsAvoid state (List.ofFn indices)) :
    columnStateValues cells
      (Circuit.forRangeRecord count
        (fun index => reduceColumn cells.tail.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.head.ref (indices index))
        (fun index => reduceColumnStep cells.tail.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.head.ref (indices index)) store).1
      (ClassicalAlgorithms.GF2.runColumns (List.ofFn indices) state) := by
  induction count generalizing store state with
  | zero => exact represented
  | succ count ih =>
      have unique : (indices 0 :: List.ofFn (fun index => indices index.succ)).Nodup := by
        simpa only [List.ofFn_succ] using nodup
      have currentAvoid : ClassicalAlgorithms.GF2.PivotColumnsAvoid state
          (indices 0 :: List.ofFn (fun index => indices index.succ)) := by
        simpa only [List.ofFn_succ] using avoid
      have absent := absent_of_avoid state (indices 0) _ currentAvoid
      have next := gf2ReduceColumn_cellState cells distinct (indices 0) store state
        represented absent
      have nextAvoid := ClassicalAlgorithms.GF2.stepColumn_pivotColumnsAvoid_tail
        (indices 0) state (List.ofFn (fun index => indices index.succ)) currentAvoid
        (List.nodup_cons.mp unique).1
      rw [List.ofFn_succ, ClassicalAlgorithms.GF2.runColumns]
      exact ih (fun index => indices index.succ) (List.nodup_cons.mp unique).2 _ _ next nextAvoid

/-- The original actual column sequence realizes the pure ordered pass in the same seven cells. -/
theorem gf2ReduceColumns_cellState
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (store : Store ctx) (state : ClassicalAlgorithms.GF2.State rowCount width)
    (represented : columnStateValues cells store state)
    (avoid : ClassicalAlgorithms.GF2.PivotColumnsAvoid state (List.finRange width)) :
    columnStateValues cells
      (Circuit.forRangeRecord width
        (reduceColumn cells.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref)
        (reduceColumnStep cells.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.head.ref
          cells.tail.tail.tail.tail.tail.tail.head.ref cells.tail.tail.tail.head.ref) store).1
      (ClassicalAlgorithms.GF2.runColumns (List.finRange width) state) := by
  have unique : (List.ofFn (id : Fin width → Fin width)).Nodup := by
    simpa only [List.ofFn_id] using List.nodup_finRange width
  have initialAvoid : ClassicalAlgorithms.GF2.PivotColumnsAvoid state
      (List.ofFn (id : Fin width → Fin width)) := by
    simpa only [List.ofFn_id] using avoid
  simpa only [List.ofFn_id, id_eq] using
    traverse cells distinct width id unique store state represented initialAvoid

end

end QuantumAlg.ClassicalRoutines.GF2.Native
