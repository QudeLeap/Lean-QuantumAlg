/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sub.Program

/-!
# Exact natural subtraction and caller frame of the actual circuit

The arbitrary incoming result word is overwritten. Only the comparison latch
and result word may change; all other structural caller reads are preserved.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSub

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact natural output, comparison flag, and complete structural caller frame. -/
def Relation (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  (after.read (writeInput refs.output)).toNat =
      (before.read refs.left).toNat - (before.read refs.right).toNat ∧
    (after.read (writeInput refs.lessThan)).toBool =
      decide ((before.read refs.left).toNat < (before.read refs.right).toNat) ∧
    ∀ {shape : CShape} (other : CInputRef ctx shape),
      refs.lessThan.key ∉ other.storageKeys → refs.output.key ∉ other.storageKeys →
        after.read other = before.read other

private lemma wordSub_toNat_eq_sub (left right : CShape.Word width)
    (rightLeLeft : right.toNat ≤ left.toNat) :
    (CShape.wordSub width left right).toNat = left.toNat - right.toNat := by
  have differenceRange : left.toNat - right.toNat < CShape.wordModulus width :=
    (Nat.sub_le _ _).trans_lt left.toNat_lt
  have wrappedSplit : left.toNat + CShape.wordModulus width - right.toNat =
      (left.toNat - right.toNat) + CShape.wordModulus width := by omega
  rw [CShape.wordSub, CShape.wordOfNat_val, wrappedSplit]
  simp [Nat.mod_eq_of_lt differenceRange]

/-- The actual comparison writes exactly the original unsigned less-than predicate. -/
lemma compare_correct (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (compareOp refs)).read (writeInput refs.lessThan)).toBool =
      decide ((store.read refs.left).toNat < (store.read refs.right).toNat) := by
  change ((store.applyOp (compareOp refs)).read
    (.storage (compareOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

private lemma clear_output (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (clearOp refs)).read (writeInput refs.output)).toNat = 0 := by
  change ((store.applyOp (clearOp refs)).read
    (.storage (clearOp refs).outputRef.toCStorageRef)).toNat = 0
  rw [Store.read_applyOp_output]
  change (CShape.wordBitXor width (store.read (writeInput refs.output))
    (store.read (writeInput refs.output))).toNat = 0
  simp [CShape.wordBitXor, CShape.wordOfNat_val]

private lemma subtract_output (refs : Refs ctx width) (store : Store ctx)
    (rightLeLeft : (store.read refs.right).toNat ≤ (store.read refs.left).toNat) :
    ((store.applyOp (subtractOp refs)).read (writeInput refs.output)).toNat =
      (store.read refs.left).toNat - (store.read refs.right).toNat := by
  change ((store.applyOp (subtractOp refs)).read
    (.storage (subtractOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact wordSub_toNat_eq_sub (store.read refs.left) (store.read refs.right) rightLeLeft

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual selected instruction changes only the result cell. -/
lemma selectedStep_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : refs.output.key ∉ other.storageKeys) :
    (selectedStep (model := model) refs store).1.read other = store.read other := by
  rw [selectedStep_store]
  split <;> exact Store.read_applyOp_of_not_mem_storageKeys store _ other separate

/-- Every caller read outside the two actual write keys retains its complete value. -/
lemma into_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoidsLessThan : refs.lessThan.key ∉ other.storageKeys)
    (avoidsOutput : refs.output.key ∉ other.storageKeys) :
    (step (model := model) refs store).1.read other = store.read other := by
  rw [step_store]
  exact (selectedStep_callerFrame refs _ other avoidsOutput).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (compareOp refs) other avoidsLessThan)

/-- The actual result is natural truncated subtraction at every word width. -/
lemma into_value (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    ((step (model := model) refs store).1.read (writeInput refs.output)).toNat =
      (store.read refs.left).toNat - (store.read refs.right).toNat := by
  have comparedFlag := compare_correct refs store
  have leftAtCompare := Store.read_applyOp_of_not_mem_storageKeys store (compareOp refs)
    refs.left separation.leftAvoidsLessThan
  have rightAtCompare := Store.read_applyOp_of_not_mem_storageKeys store (compareOp refs)
    refs.right separation.rightAvoidsLessThan
  rw [step_store, selectedStep_store]
  split
  · rename_i selected
    have underflow : (store.read refs.left).toNat < (store.read refs.right).toNat :=
      of_decide_eq_true (comparedFlag.symm.trans selected)
    rw [clear_output, Nat.sub_eq_zero_of_le (Nat.le_of_lt underflow)]
  · rename_i selected
    have rightLeLeft : (store.read refs.right).toNat ≤ (store.read refs.left).toNat := by
      apply Nat.le_of_not_gt
      intro underflow
      exact selected (comparedFlag.trans (decide_eq_true underflow))
    rw [subtract_output refs _ (by simpa only [leftAtCompare, rightAtCompare] using rightLeLeft),
      leftAtCompare, rightAtCompare]

/-- The selected output write preserves the actual comparison latch. -/
lemma into_flag (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    ((step (model := model) refs store).1.read (writeInput refs.lessThan)).toBool =
      decide ((store.read refs.left).toNat < (store.read refs.right).toNat) := by
  rw [step_store]
  exact (congrArg CShape.Value.toBool
    (selectedStep_callerFrame refs _ (writeInput refs.lessThan)
      separation.lessThanAvoidsOutput)).trans (compare_correct refs store)

/-- The actual execution record satisfies the complete original arithmetic and caller contract. -/
lemma into_correct (refs : Refs ctx width) (separation : Separation refs) (store : Store ctx) :
    Relation refs store (step (model := model) refs store).1 :=
  ⟨into_value refs separation store, into_flag refs separation store,
    fun other avoidsFlag avoidsOutput => into_callerFrame refs store other avoidsFlag avoidsOutput⟩

/-- Width zero still executes comparison and subtraction, returning zero and a false latch. -/
lemma into_zero_width (refs : Refs ctx 0) (separation : Separation refs) (store : Store ctx) :
    ((step (model := model) refs store).1.read (writeInput refs.output)).toNat = 0 ∧
      ((step (model := model) refs store).1.read (writeInput refs.lessThan)).toBool = false := by
  have left : (store.read refs.left).toNat = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (store.read refs.left).toNat_lt)
  have right : (store.read refs.right).toNat = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (store.read refs.right).toNat_lt)
  constructor
  · simpa only [left, right, Nat.sub_self] using into_value refs separation store
  · simpa only [left, right, Nat.lt_irrefl, decide_false] using into_flag refs separation store

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSub
