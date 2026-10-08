/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Layout
import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Program
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Actual finite binary-refinement iteration

The existing iterate instruction executes the same refinement round at each
stage. Its record contains the actual store and stored-flag path at every index.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {inputWidth : Nat}

/-- Execute the specified finite number of actual binary-refinement rounds. -/
def roundsInto (refs : Refs ctx inputWidth) (remaining : Nat) : Circuit model ctx ctx :=
  .iterate remaining (IntegerSqrt.roundInto (model := model) (wideInput refs) refs.round)

/-- The actual final store and chronological vector of selected round paths. -/
def roundsStep (refs : Refs ctx inputWidth) (remaining : Nat) (store : Store ctx) :
    Store ctx × (roundsInto (model := model) refs remaining).Path :=
  let advance := fun before => (IntegerSqrt.roundStep (model := model) (wideInput refs) refs.round
    before).1
  (advance^[remaining] store,
    fun index => (IntegerSqrt.roundStep (model := model) (wideInput refs) refs.round
      (advance^[index.val] store)).2)

/-- Zero refinement rounds preserve the complete input store. -/
theorem roundsStep_zero_store (refs : Refs ctx inputWidth) (store : Store ctx) :
    (roundsStep (model := model) refs 0 store).1 = store := rfl

/-- One successor iteration executes its actual head round before the remaining rounds. -/
theorem roundsStep_succ_store (refs : Refs ctx inputWidth) (remaining : Nat)
    (store : Store ctx) :
    (roundsStep (model := model) refs (remaining + 1) store).1 =
      (roundsStep (model := model) refs remaining (IntegerSqrt.roundStep (model := model)
        (wideInput refs) refs.round store).1).1 :=
  Function.iterate_succ_apply _ _ _

/-- The finite actual loop preserves all incoming histories and quantum-reference blocks. -/
theorem roundsInto_execute (refs : Refs ctx inputWidth) (remaining : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (roundsInto (model := model) refs remaining).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := roundsStep (model := model) refs remaining entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  let nativeStep := IntegerSqrt.roundStep (model := model) (wideInput refs) refs.round
  let jointStep := fun before : Store ctx × model.HiddenState =>
    let actual := nativeStep before.1
    ((actual.1, before.2), actual.2)
  have iterated (count : Nat) (store : Store ctx) (hidden : model.HiddenState) :
      ((fun before => (jointStep before).1)^[count]) (store, hidden) =
        (((fun before => (nativeStep before).1)^[count]) store, hidden) := by
    induction count generalizing store with
    | zero => rfl
    | succ count ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        exact ih (nativeStep store).1
  refine (Circuit.execute_iterate_mapClassical
    (IntegerSqrt.roundInto (model := model) (wideInput refs) refs.round) jointStep
    (fun reference _history _ current =>
      IntegerSqrt.roundInto_execute (wideInput refs) refs.round reference current)
    remaining Reference state).trans ?_
  apply ExecutionState.executionState_mapClassical_congr
  funext entry
  simp only [iterated]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
