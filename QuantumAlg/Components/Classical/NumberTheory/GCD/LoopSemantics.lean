/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.GuardedRemainder
import all QuantumAlg.Core.Execution.Classical.Iteration
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Actual Euclidean iteration and its total mathematical recurrence

The selected store update is repeated by the existing circuit iterate
instruction. Its recorded paths come from the actual store at each stage.
The internally established ready invariant is preserved at every count, and
the two stored words agree with the original terminating Euclidean recurrence.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution
open ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual selected-store iteration and the body path produced at each finite stage. -/
def iteratedRemainderStep (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) (store : Store ctx) : Store ctx ×
      (Circuit.iterate count (guardedRemainder (model := model) first second zero active)).Path :=
  let step := guardedRemainderStep (model := model) first second zero active
  ((fun value => (step value).1)^[count] store,
    fun index => (step ((fun value => (step value).1)^[index.val] store)).2)

/-- The native iteration has exactly its computed final store and actual finite path vector. -/
theorem gcdLoop_execute (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (count : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.iterate count (guardedRemainder (model := model) first second zero active)).execute
      Reference state =
      state.mapClassical (fun entry =>
        let result := iteratedRemainderStep (model := model) first second zero active count entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  let nativeStep := guardedRemainderStep (model := model) first second zero active
  let jointStep := fun before : Store ctx × model.HiddenState =>
    let result := nativeStep before.1
    ((result.1, before.2), result.2)
  have iterated (count : Nat) (store : Store ctx) (hidden : model.HiddenState) :
      ((fun before => (jointStep before).1)^[count]) (store, hidden) =
        (((fun before => (nativeStep before).1)^[count]) store, hidden) := by
    induction count generalizing store with
    | zero => rfl
    | succ count ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih (nativeStep store).1
  refine (Circuit.execute_iterate_mapClassical
    (guardedRemainder (model := model) first second zero active) jointStep
    (fun reference history _ initial => by
      exact (gcdGuardedRemainder_execute (model := model)
        first second zero active reference initial).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)) count Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  simp only [iterated]
  rfl


/-- Internal initialization is preserved through every actual iteration count. -/
theorem gcdLoop_ready (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (count : Nat) (store : Store ctx)
    (ready : storedEuclidReady first zero active store) :
    storedEuclidReady first zero active
      (iteratedRemainderStep (model := model) first second zero active count store).1 := by
  change storedEuclidReady first zero active
    ((fun value => (guardedRemainderStep (model := model) first second zero active
      value).1)^[count] store)
  induction count generalizing store with
  | zero => exact ready
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (gcdGuardedRemainder_store_transition first second zero active
        firstSecond activeFirst activeSecond firstZero secondZero activeZero store ready).1

/-- Every actual iteration count agrees with the existing pure terminating Euclidean run. -/
theorem gcdLoop_state (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (count : Nat) (store : Store ctx)
    (ready : storedEuclidReady first zero active store) :
    storedEuclidState first second
      (iteratedRemainderStep (model := model) first second zero active count store).1 =
      Euclid.run count (storedEuclidState first second store) := by
  change storedEuclidState first second
      ((fun value => (guardedRemainderStep (model := model) first second zero active
        value).1)^[count] store) = _
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      by_cases finished : (storedEuclidState first second store).first = 0
      · have fixed : (guardedRemainderStep (model := model) first second zero active store).1 =
        store := by
          rw [gcdGuardedRemainder_step_store, ready.2]
          have divisorZero : (store.read (cellRead first)).toNat = 0 := finished
          simp [divisorZero]
        rw [Function.iterate_fixed fixed]
        exact (if_pos finished).symm
      · have transition := gcdGuardedRemainder_store_transition first second zero active
          firstSecond activeFirst activeSecond firstZero secondZero activeZero store ready
        rw [Function.iterate_succ_apply, ih _ transition.1, transition.2, if_neg finished]
        exact (if_neg finished).symm

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
