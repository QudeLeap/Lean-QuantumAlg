/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.RetainedSemantics
import all QuantumAlg.Core.Execution.Borrowed.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Original reads and complete borrowed restoration of native GCD

All writes target either the freshly retained result or the actual lexical
cells. The store equations therefore preserve every original structural read.
The same actual transformation preserves the borrowed classical value, which
together with the exact block equation proves joint restoration of borrowed
classical storage, quantum systems and the external reference.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

private lemma guarded_read_other (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (store : Store ctx) :
    (guardedRemainderStep (model := model) first second zero active store).1.read other =
      store.read other := by
  rw [gcdGuardedRemainder_step_store]
  split
  · exact gcdScopedRemainder_read_other first second zero active other
      firstFree secondFree activeFree store
  · rfl

private lemma iterated_read_other (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    {shape : CShape} (other : CInputRef ctx shape)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (count : Nat) (store : Store ctx) :
    (iteratedRemainderStep (model := model) first second zero active count store).1.read other =
      store.read other := by
  change ((fun value => (guardedRemainderStep (model := model) first second zero active
    value).1)^[count]
    store).read other = _
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, ih]
      exact guarded_read_other first second zero active other firstFree secondFree activeFree store

private lemma scheduled_read_other (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    {shape : CShape} (other : CInputRef ctx shape)
    (firstFree : first.key ∉ other.storageKeys) (secondFree : second.key ∉ other.storageKeys)
    (activeFree : active.key ∉ other.storageKeys) (resultFree : result.key ∉ other.storageKeys)
    (store : Store ctx) :
    (scheduledStep (model := model) input first second active result store).1.read other =
      store.read other := by
  change ((iteratedRemainderStep (model := model) first second (cellRead result) active
    (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (initializationStore input first second (cellRead result) active store)).1.applyOp
        (.wordUnary .copy width ctx (cellRead second) result)).read other = _
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (.wordUnary .copy width ctx (cellRead second) result) other resultFree]
  exact (iterated_read_other first second (cellRead result) active other
    firstFree secondFree activeFree _ _).trans
    (gcdInitialization_read_other input first second (cellRead result) active other
      firstFree secondFree activeFree store)

/-- Lexical execution preserves every parent read that excludes the actual result cell. -/
lemma gcdLexical_read_other (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) {shape : CShape}
    (other : CInputRef ctx shape) (resultFree : result.key ∉ other.storageKeys)
    (store : Store ctx) :
    (lexicalStep (model := model) input result store).1.read other = store.read other := by
  have separated := gcdLayout_input_separation other width
  have liftedKey : (writeUnderLoop result width).key = result.key := rfl
  have liftedFree : (writeUnderLoop result width).key ∉ (underLoop other width).storageKeys := by
    simpa only [gcdLayout_underLoop_keys, liftedKey] using resultFree
  have exited := gcdLayout_pop_read other width
    (scheduledStep (model := model) (underLoop input width) (currentCell ctx width) (previousCell
      ctx width)
      (conditionCell ctx width) (writeUnderLoop result width) (pushLoopStore width store)).1
  exact exited.trans ((scheduled_read_other (underLoop input width)
    (currentCell ctx width) (previousCell ctx width) (conditionCell ctx width)
    (writeUnderLoop result width) (underLoop other width)
    separated.1 separated.2.1 separated.2.2 liftedFree (pushLoopStore width store)).trans
    (gcdLayout_push_read other width store))

/-- The complete retained algorithm preserves every original structural classical read. -/
lemma gcdRetained_read_original (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) :
    (retainedStep (model := model) input key fresh store).1.read
      (other.underRetained key (.unsignedWord width) fresh) = store.read other :=
  (gcdLexical_read_other (input.underRetained key (.unsignedWord width) fresh)
    (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh)
    (other.underRetained key (.unsignedWord width) fresh)
    (CInputRef.fresh_not_mem_storageKeys_underRetained other key (.unsignedWord width) fresh)
    (store.pushRetained key (.unsignedWord width) fresh)).trans
    (Store.read_pushRetained_underRetained store key (.unsignedWord width) fresh other)

private lemma scoped_borrowed (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) :
    (scopedRemainderStep (model := model) first second zero active store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [scopedRemainderStep, remainderStep, BitWord.instructionStep,
    Store.readBorrowedClassical_popWorkspace,
    Store.readBorrowedClassical_applyOp, Store.readBorrowedClassical_pushWorkspace]

private lemma guarded_borrowed (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) :
    (guardedRemainderStep (model := model) first second zero active store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  rw [gcdGuardedRemainder_step_store]
  split
  · exact scoped_borrowed first second zero active store
  · rfl

private lemma iterated_borrowed (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) (store : Store ctx) :
    (iteratedRemainderStep (model := model) first second zero active count
      store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  change ((fun value => (guardedRemainderStep (model := model) first second zero active
    value).1)^[count]
    store).readBorrowedClassical = _
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, ih]
      exact guarded_borrowed first second zero active store

private lemma scheduled_borrowed (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (scheduledStep (model := model) input first second active result
      store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [scheduledStep, initializationStep, BitWord.instructionStep,
    Store.readBorrowedClassical_applyOp, iterated_borrowed]

/-- The actual lexical step preserves every borrowed classical value. -/
lemma gcdLexical_borrowed_values (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (lexicalStep (model := model) input result store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  let final := (scheduledStep (model := model) (underLoop input width) (currentCell ctx width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
    (pushLoopStore width store)).1
  have exited : (popLoopStore width final).readBorrowedClassical =
      final.readBorrowedClassical := rfl
  have entered : (pushLoopStore width store).readBorrowedClassical =
      store.readBorrowedClassical := rfl
  exact exited.trans ((scheduled_borrowed (underLoop input width) (currentCell ctx width)
    (previousCell ctx width) (conditionCell ctx width) (writeUnderLoop result width)
    (pushLoopStore width store)).trans entered)

/-- The lexical body restores the complete borrowed classical-quantum-reference observation. -/
lemma gcdLexical_borrowedRestored (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (lexicalBody (model := model) input result).BorrowedRestored Reference state
      ((lexicalBody (model := model) input result).execute environment Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, gcdLexical_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState × (History × (lexicalBody (model := model) input result).Path)) state
    (fun entry =>
      let next := lexicalStep (model := model) input result entry.1
      (next.1, (entry.2.1, (entry.2.2, next.2))))
    (fun entry => gcdLexical_borrowed_values input result entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- Actual retained GCD restores all borrowed systems jointly with every external reference. -/
lemma gcdRetained_borrowedRestored (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) {environment : model.Environment}
    (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (retainedCircuit (model := model) input key fresh).BorrowedRestored Reference state
      ((retainedCircuit (model := model) input key fresh).execute environment Reference state) := by
  unfold retainedCircuit
  apply Circuit.borrowedRestored_seq (environment := environment)
  · exact Circuit.borrowedRestored_retain
      (environment := environment) key (.unsignedWord width) fresh state
  · exact gcdLexical_borrowedRestored _ _ Reference _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
