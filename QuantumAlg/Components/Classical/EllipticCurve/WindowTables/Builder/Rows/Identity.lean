/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Row
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Columns
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Exact actual identity row in all five original columns

The original five paid vector overwrites write the actual protected zero
input into every physical column, including the fifth x-plus-one column.
All other rows survive. The complete chronological record retains every
incoming quantum/reference/history block and the original service state.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : TableFrame ctx width length)

private def clearIdentityBody (row : Fin length) : Fin 5 → Circuit model ctx ctx :=
  ![BitWord.instruction (execution := model) (rowWriteOp frame.arrays.x row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.y row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.c row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.d row frame.zero),
    BitWord.instruction (execution := model) (rowWriteOp frame.arrays.e row frame.zero)]

private def clearIdentityStep (row : Fin length) (column : Fin 5) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (frame.clearIdentityBody (model := model) row column).Path := by
  refine Fin.cases ?_ (fun second => ?_) column
  · exact Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
      (rowWriteOp frame.arrays.x row frame.zero))
  · refine Fin.cases ?_ (fun third => ?_) second
    · exact Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
        (rowWriteOp frame.arrays.y row frame.zero))
    · refine Fin.cases ?_ (fun fourth => ?_) third
      · exact Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
          (rowWriteOp frame.arrays.c row frame.zero))
      · refine Fin.cases ?_ (fun fifth => ?_) fourth
        · exact Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
            (rowWriteOp frame.arrays.d row frame.zero))
        · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) fifth
          exact Circuit.preserveHiddenRecord (BitWord.instructionStep (execution := model)
            (rowWriteOp frame.arrays.e row frame.zero))

private lemma clearIdentityStep_store (row : Fin length) (column : Fin 5)
    (before : Store ctx × model.HiddenState) :
    (frame.clearIdentityStep (model := model) row column before).1.1 =
      before.1.applyOp (rowWriteOp (frame.arrays.column column) row frame.zero) := by
  fin_cases column <;> rfl

/-- Original five native overwrites with their true chronological Stores and paths. -/
def clearIdentityRecord (row : Fin length) : Store ctx × model.HiddenState →
    (Store ctx × model.HiddenState) × (frame.clearIdentityRow (model := model) row).Path :=
  Circuit.forRangeRecord 5 (frame.clearIdentityBody row) (frame.clearIdentityStep row)

/-- The literal original clear-row program executes exactly this complete retained record. -/
lemma clearIdentityRow_execute (row : Fin length) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.clearIdentityRow (model := model) row).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.clearIdentityRecord row (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine Circuit.execute_forRangeRecord 5 (frame.clearIdentityBody row) environment
    (frame.clearIdentityStep row) ?_ Reference state
  intro column reference history historyFinite initial
  fin_cases column
  all_goals
    exact (BitWord.bitWord_instruction_execute (environment := environment)
      (execution := model) _ initial).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)

omit [BitWord.Selected model] in
private lemma column_zero_free (column : Fin 5) :
    (frame.arrays.column column).key ∉ frame.zero.storageKeys := by
  fin_cases column <;> exact frame.protectedReads frame.zero (by simp) _ (by simp [Arrays.column])

/-- Every actual column receives the same original protected zero input, even the fifth column. -/
lemma clearIdentityRecord_values (row : Fin length) (before : Store ctx × model.HiddenState) :
    ∀ column : Fin 5,
      (frame.clearIdentityRecord (model := model) row before).1.1.read
        (rowRead (frame.arrays.column column) row) = before.1.read frame.zero := by
  have completed := Circuit.forRangeRecord_invariant 5
    (frame.clearIdentityBody row) (frame.clearIdentityStep row)
    (fun processed current => current.1.read frame.zero = before.1.read frame.zero ∧
      ∀ column : Fin 5, column.val < processed →
        current.1.read (rowRead (frame.arrays.column column) row) = before.1.read frame.zero)
    (fun index current established => by
      rw [frame.clearIdentityStep_store]
      refine ⟨(Store.read_applyOp_of_not_mem_storageKeys current.1
        (rowWriteOp (frame.arrays.column index) row frame.zero) frame.zero
        (frame.column_zero_free index)).trans established.1, ?_⟩
      intro column visited
      by_cases same : column = index
      · subst column
        exact (rowWrite_read_same _ _ _ current.1).trans established.1
      · exact (rowWrite_read_array _ _ _ _ _ current.1
          (frame.arrays.column_key_ne index column (Ne.symm same))).trans
          (established.2 column (by
            have unequal : column.val ≠ index.val := fun equal => same (Fin.ext equal)
            omega)))
    before ⟨rfl, by intro column impossible; omega⟩
  exact fun column => completed.2 column column.isLt

/-- No other actual array row is changed by any of the original five overwrites. -/
lemma clearIdentityRecord_read_other_row (selected : Fin length)
    (before : Store ctx × model.HiddenState)
    (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (row : Fin length) (different : row ≠ selected) :
    (frame.clearIdentityRecord (model := model) selected before).1.1.read (rowRead array row) =
      before.1.read (rowRead array row) := by
  exact Circuit.forRangeRecord_invariant 5
    (frame.clearIdentityBody selected) (frame.clearIdentityStep selected)
    (fun _ current => current.1.read (rowRead array row) = before.1.read (rowRead array row))
    (fun index current established => by
      rw [frame.clearIdentityStep_store]
      exact (rowWrite_read_of_row_ne _ _ _ _ _ current.1 different).trans established)
    before rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
