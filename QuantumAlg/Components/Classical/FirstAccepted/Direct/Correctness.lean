/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Direct

/-!
# Exact first-success meaning of actual stored-bit selection
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted.Direct

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma eligibleArmStep_store (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (eligibleArmStep (model := model) eligible candidate refs value store).1 =
      if value.toBool then
        (store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)
      else store := by
  cases value with
  | bit value => cases value <;> rfl

private lemma pendingArmStep_store (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (value : CShape.Value .bit) (store : Store ctx) :
    (pendingArmStep (model := model) eligible candidate refs value store).1 =
      if value.toBool then store
      else if (store.read eligible).toBool then
        (store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)
      else store := by
  cases value with
  | bit value =>
      cases value
      · exact eligibleArmStep_store eligible candidate refs (store.read eligible) store
      · rfl

/-- Actual first-success execution changes only the store selected by its two existing
predicates. -/
lemma step_store (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    (step (model := model) eligible candidate refs store).1 =
      if (store.read (writeInput refs.accepted)).toBool then store
      else if (store.read eligible).toBool then
        (store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)
      else store :=
  pendingArmStep_store eligible candidate refs (store.read (writeInput refs.accepted)) store

/-- All actual caller reads outside the two persistent results survive first-success selection. -/
lemma into_callerFrame (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (step (model := model) eligible candidate refs store).1 := by
  intro shape other acceptedFree selectedFree
  rw [step_store]
  split
  · rfl
  · split
    · exact (Store.read_applyOp_of_not_mem_storageKeys _ (acceptedOp eligible refs)
        other acceptedFree).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (selectedOp candidate refs)
          other selectedFree)
    · rfl

/-- Original first-success latches and full caller reads, expressed using actual stored input
values. -/
structure Outcome {kind : ProblemKind} {ctx : RuntimeCtx kind} (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (before after : Store ctx) : Prop where
  accepted : (after.read (writeInput refs.accepted)).toBool =
    ((before.read (writeInput refs.accepted)).toBool || (before.read eligible).toBool)
  selected : after.read (writeInput refs.selected) =
    if (!(before.read (writeInput refs.accepted)).toBool && (before.read eligible).toBool) then
      before.read candidate else before.read (writeInput refs.selected)
  callerFrame : CallerFrame refs before after

/-- Actual stored-bit control preserves an earlier choice and takes exactly the first eligible
input. -/
lemma into_correct (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (separation : Separation eligible candidate refs) (store : Store ctx) :
    Outcome eligible candidate refs store (step (model := model) eligible candidate refs store).1
      := by
  have selectedFree : refs.accepted.key ∉ (writeInput refs.selected).storageKeys := by
    simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton] using
      separation.acceptedNeSelected
  have selectedResult :
      (((store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)).read
        (writeInput refs.selected)) = store.read candidate := by
    rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ selectedFree]
    exact Store.read_applyOp_output store (selectedOp candidate refs)
  have acceptedResult :
      (((store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)).read
        (writeInput refs.accepted)).toBool = (store.read eligible).toBool := by
    change (((store.applyOp (selectedOp candidate refs)).applyOp (acceptedOp eligible refs)).read
      (.storage (acceptedOp eligible refs).outputRef.toCStorageRef)).toBool = _
    rw [Store.read_applyOp_output]
    change ((store.applyOp (selectedOp candidate refs)).read eligible).toBool = _
    rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ separation.eligibleAvoidsSelected]
  refine ⟨?_, ?_, into_callerFrame eligible candidate refs store⟩
  · rw [step_store]
    cases accepted : (store.read (writeInput refs.accepted)).toBool <;>
      cases eligibleValue : (store.read eligible).toBool <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.false_or, Bool.true_or,
          acceptedResult, eligibleValue, accepted]
  · rw [step_store]
    cases accepted : (store.read (writeInput refs.accepted)).toBool <;>
      cases eligibleValue : (store.read eligible).toBool <;>
        simp only [Bool.false_eq_true, if_false, if_true, Bool.not_false, Bool.not_true,
          Bool.true_and, Bool.false_and, selectedResult]

/-- Both original source inputs survive the actual chosen branch under structural separation. -/
lemma into_source_frame (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord width)) (refs : Refs ctx width)
    (separation : Separation eligible candidate refs) (store : Store ctx) :
    (step (model := model) eligible candidate refs store).1.read eligible = store.read eligible ∧
      (step (model := model) eligible candidate refs store).1.read candidate = store.read candidate
        :=
  ⟨into_callerFrame eligible candidate refs store eligible separation.eligibleAvoidsAccepted
      separation.eligibleAvoidsSelected,
    into_callerFrame eligible candidate refs store candidate separation.candidateAvoidsAccepted
      separation.candidateAvoidsSelected⟩

end

end QuantumAlg.ClassicalRoutines.FirstAccepted.Direct
