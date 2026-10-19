/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Eliminate
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Invariant

/-!
# Complete records of actual selected-pivot row elimination

The original stored matrix bit selects each actual row-XOR. Full store,
reference and history correlations follow that same record, including every
unchanged branch. No hypothesis asserts that the supplied pivot is valid;
the actual conditional matrix transformation is total on all nominal words.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {environment : model.Environment}
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- Actual selected instruction and its same-context path. -/
def eliminationChoiceStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (eliminationChoice matrix pivot target value).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true =>
      BitWord.instructionStep (execution := model)
        (eliminationXorOp matrix pivot target) store

private lemma eliminationChoice_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (eliminationChoice (model := model) matrix pivot target value).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((eliminationChoiceStep matrix pivot target value entry.1).1,
          (entry.2.1, (entry.2.2,
            (eliminationChoiceStep matrix pivot target value entry.1).2)))) := by
  cases value with
  | bit bit =>
      cases bit
      · refine (Circuit.execute_id_mapClassical
        (environment := environment) (model := model) Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
          (eliminationXorOp matrix pivot target) state

private def staticRecord (condition : Prop) (decision : Decidable condition)
    (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    Store ctx × (@ite (Circuit model ctx ctx) condition decision first second).Path :=
  match decision with
  | .isTrue _ => firstStep store
  | .isFalse _ => secondStep store

omit [BitWord.Selected model] in
private lemma staticRecord_store (condition : Prop) (decision : Decidable condition)
    (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path) (store : Store ctx) :
    (staticRecord condition decision first second firstStep secondStep store).1 =
      @ite (Store ctx) condition decision (firstStep store).1 (secondStep store).1 := by
  cases decision <;> rfl

omit [BitWord.Selected model] in
private lemma staticRecord_execute (condition : Prop) (decision : Decidable condition)
    (first second : Circuit model ctx ctx)
    (firstStep : Store ctx → Store ctx × first.Path)
    (secondStep : Store ctx → Store ctx × second.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)), first.execute environment
        Reference state =
        state.mapClassical (fun entry =>
          ((firstStep entry.1).1, (entry.2.1, (entry.2.2, (firstStep entry.1).2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)), second.execute environment
        Reference state =
        state.mapClassical (fun entry =>
          ((secondStep entry.1).1, (entry.2.1, (entry.2.2, (secondStep entry.1).2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (@ite (Circuit model ctx ctx) condition decision first second).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((staticRecord condition decision first second firstStep secondStep entry.1).1,
          (entry.2.1, (entry.2.2,
            (staticRecord condition decision first second firstStep secondStep entry.1).2)))) := by
  cases decision with
  | isTrue _ => exact firstEquation Reference state
  | isFalse _ => exact secondEquation Reference state

/-- The actual target record contains its genuine stored-bit branch, except at the skipped pivot. -/
def eliminateTargetStep (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (eliminateTarget matrix pivot target column).Path :=
  staticRecord (target = pivot) (instDecidableEqFin rowCount target pivot)
    (.id (model := model) ctx)
    (.branch (eliminationBit matrix target column)
      (eliminationChoice (model := model) matrix pivot target))
    (fun current => (current, ()))
    (fun current =>
      let value := current.read (eliminationBit matrix target column)
      let actual := eliminationChoiceStep matrix pivot target value current
      (actual.1, ⟨value, actual.2⟩)) store

/-- Every complete quantum-reference block follows the original actual target decision. -/
lemma gf2EliminateTarget_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (eliminateTarget (model := model) matrix pivot target column).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        ((eliminateTargetStep matrix pivot target column entry.1).1,
          (entry.2.1, (entry.2.2,
            (eliminateTargetStep matrix pivot target column entry.1).2)))) := by
  exact staticRecord_execute (target = pivot) (instDecidableEqFin rowCount target pivot)
    (.id (model := model) ctx)
    (.branch (eliminationBit matrix target column)
      (eliminationChoice (model := model) matrix pivot target))
    (fun current => (current, ()))
    (fun current =>
      let value := current.read (eliminationBit matrix target column)
      let actual := eliminationChoiceStep matrix pivot target value current
      (actual.1, ⟨value, actual.2⟩))
    (fun reference {_} _ current => by
      refine (Circuit.execute_id_mapClassical
        (environment := environment) (model := model) reference current).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ current =>
      Circuit.execute_branchStoreRecord
        (environment := environment) (model := model) (eliminationBit matrix target column)
        (eliminationChoice (model := model) matrix pivot target)
        (eliminationChoiceStep matrix pivot target)
        (eliminationChoice_execute (model := model) matrix pivot target) reference current)
    Reference state

omit [BitWord.Selected model] in
/-- The actual bit read has exactly the original MSB-first logical column coordinate. -/
lemma gf2EliminationBit_value
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (target : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (store.read (eliminationBit matrix target column)).toBool =
      ((store.read (.storage matrix.toCStorageRef)).get target).toNat.testBit
        (width - 1 - column.val) := by
  change (((store.read (.storage matrix.toCStorageRef)).get target).wordBitGet column).toBool = _
  cases (store.read (.storage matrix.toCStorageRef)).get target
  rfl

/-- The complete store changes only through the original conditionally executed matrix XOR. -/
lemma gf2EliminateTarget_store
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (eliminateTargetStep matrix pivot target column store).1 =
      if target = pivot then store
      else if (store.read (eliminationBit matrix target column)).toBool then
        store.write matrix (CShape.vectorRowXor (store.read (.storage matrix.toCStorageRef))
          pivot target)
      else store := by
  dsimp only [eliminateTargetStep]
  rw [staticRecord_store]
  by_cases same : target = pivot
  · simp only [if_pos same]
  · simp only [if_neg same]
    cases selected : store.read (eliminationBit matrix target column) with
    | bit bit => cases bit <;> rfl

/-- Every structural caller read outside the actual matrix key is preserved. -/
lemma gf2EliminateTarget_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot target : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : matrix.key ∉ other.storageKeys) :
    (eliminateTargetStep matrix pivot target column store).1.read other = store.read other := by
  rw [gf2EliminateTarget_store]
  split
  · rfl
  · split
    · exact Store.read_write_of_not_mem_storageKeys store matrix _ other separate
    · rfl

/-- Actual successive target records retain their intermediate stores and branch histories. -/
def eliminateWithPivotStep
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    Store ctx × (eliminateWithPivot matrix pivot column).Path :=
  Circuit.forRangeStoreRecord rowCount
    (fun target => eliminateTarget (model := model) matrix pivot target column)
    (fun target => eliminateTargetStep matrix pivot target column) store

/-- The full target pass preserves every original Store/Reference/History correlation. -/
lemma gf2EliminateWithPivot_execute
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (eliminateWithPivot (model := model) matrix pivot column).execute environment Reference state =
      state.mapClassical (fun entry =>
        ((eliminateWithPivotStep matrix pivot column entry.1).1,
          (entry.2.1, (entry.2.2,
            (eliminateWithPivotStep matrix pivot column entry.1).2)))) :=
  Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) rowCount _ _
    (fun target => gf2EliminateTarget_execute (model := model) matrix pivot target column)
    Reference state

/-- Every target uses its actual current matrix in the original chronological fold. -/
lemma gf2EliminateWithPivot_store
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx) :
    (eliminateWithPivotStep matrix pivot column store).1 =
      (List.ofFn (fun target : Fin rowCount => fun current : Store ctx =>
        if target = pivot then current
        else if (current.read (eliminationBit matrix target column)).toBool then
          current.write matrix (CShape.vectorRowXor
            (current.read (.storage matrix.toCStorageRef)) pivot target)
        else current)).foldl (fun current update => update current) store := by
  refine (Circuit.forRangeStoreRecord_store rowCount _ _ store).trans ?_
  congr 2
  funext target current
  exact gf2EliminateTarget_store matrix pivot target column current

/-- The whole actual target pass preserves every original non-matrix structural read. -/
lemma gf2EliminateWithPivot_read_other
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (pivot : Fin rowCount) (column : Fin width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : matrix.key ∉ other.storageKeys) :
    (eliminateWithPivotStep matrix pivot column store).1.read other = store.read other :=
  Circuit.forRangeStoreRecord_invariant rowCount _ _
    (fun _ current => current.read other = store.read other)
    (fun target current preserved =>
      (gf2EliminateTarget_read_other matrix pivot target column current other separate).trans
        preserved)
    store rfl

end

end QuantumAlg.ClassicalRoutines.GF2.Native
