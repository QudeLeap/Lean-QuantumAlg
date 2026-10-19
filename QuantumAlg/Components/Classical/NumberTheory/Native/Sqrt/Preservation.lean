/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Semantics
import all QuantumAlg.Components.Classical.ConstantWord.Preservation
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete borrowed restoration of the actual native square root

Every actual instruction writes an intrinsically writable cell. The literal
loader, selected rounds and final copy preserve the complete ordered borrowed
classical value; the matching scope pushes and pops preserve that same value.
The proved full-state equation consequently restores all borrowed classical
and quantum systems jointly with every external reference, without assuming
that the incoming state or any of its stored values is independent.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma select_borrowed (refs : RoundRefs ctx width) (store : Store ctx) :
    (selectStep (model := model) refs store).1.readBorrowedClassical = store.readBorrowedClassical
      := by
  unfold selectStep selectBodyStep BitWord.instructionStep
  cases flagRead : store.read (.storage refs.tooLarge.toCStorageRef) with
  | bit flag =>
      cases flag with
      | false => exact Store.readBorrowedClassical_applyOp store (copyOp refs)
      | true => rfl

/-- Every actual round preserves the complete actual borrowed classical tuple. -/
lemma nativeSqrt_round_borrowed_values
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (store : Store ctx) :
    (roundStep (model := model) input refs store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [roundStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    select_borrowed]

/-- The true finite round schedule keeps every borrowed classical value at every count. -/
lemma nativeSqrt_iteration_borrowed_values
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) (store : Store ctx) :
    (iteratedRoundStep (model := model) input refs count store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  change ((fun current => (roundStep (model := model) input refs current).1)^[count]
    store).readBorrowedClassical = _
  induction count generalizing store with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact (inductionHypothesis _).trans (nativeSqrt_round_borrowed_values input refs store)

/-- Widening, literal initialization, real rounds and final output all preserve borrowed values. -/
lemma nativeSqrt_body_borrowed_values (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx width)) :
    (bodyStep (model := model) input output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [bodyStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    nativeSqrt_iteration_borrowed_values,
    ConstantWord.constantWord_foldStep_borrowed_values]

omit [BitWord.Selected model] in
private lemma push_borrowed (width : Nat) (store : Store ctx) :
    (pushStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

omit [BitWord.Selected model] in
private lemma pop_borrowed (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

/-- The actual matched lexical releases return the complete original borrowed classical tuple. -/
lemma nativeSqrt_into_borrowed_values (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) input output store).1.readBorrowedClassical =
      store.readBorrowedClassical :=
  (pop_borrowed width (bodyStep (model := model) input output (pushStore width store)).1).trans
    ((nativeSqrt_body_borrowed_values input output (pushStore width store)).trans
      (push_borrowed width store))

/-- The selected copy or identity restores every borrowed system jointly. -/
private lemma select_restored (refs : RoundRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (select (model := model) refs).BorrowedRestored Reference state
      ((select (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment)
  intro value _history _ current
  cases value with
  | bit flag =>
      cases flag
      · exact Circuit.borrowedRestored_classical (environment := environment) _ current
      · exact Circuit.borrowedRestored_id (environment := environment) current

/-- Actual refinement preserves the full borrowed state through all native dependencies. -/
private lemma round_restored
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (round (model := model) input refs).BorrowedRestored Reference state
      ((round (model := model) input refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical (environment := environment) _ _
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical (environment := environment) _ _
    · apply Circuit.borrowedRestored_seq
      · exact Circuit.borrowedRestored_classical (environment := environment) _ _
      · exact Circuit.borrowedRestored_seq
          (environment := environment) _ _ _ (select_restored refs Reference _)
          (Circuit.borrowedRestored_classical (environment := environment) _ _)

/-- All borrowed classical and quantum systems return jointly with every external reference. -/
lemma nativeSqrt_into_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) input output).BorrowedRestored Reference state
      ((into (model := model) input output).execute environment Reference state) := by
  unfold into
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history0 _ current0
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history1 _ current1
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history2 _ current2
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history3 _ current3
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history4 _ current4
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro _history5 _ current5
  unfold body
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical (environment := environment) _ _
  · apply Circuit.borrowedRestored_seq
    · exact ConstantWord.constantWord_fold_borrowedRestored _ _ Reference _
    · apply Circuit.borrowedRestored_seq
      · apply Circuit.borrowedRestored_iterate (environment := environment)
        intro _history _ initial
        exact round_restored _ _ Reference initial
      · exact Circuit.borrowedRestored_classical (environment := environment) _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
