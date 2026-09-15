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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

private theorem roundsMapClassical_decision {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (first second : DecidableEq D) (state : ExecutionState C R)
    (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R first state update =
      @ExecutionState.mapClassical C D _ _ R second state update := by
  cases Subsingleton.elim first second
  rfl

/-- Execute the specified finite number of actual binary-refinement rounds. -/
def roundsInto (refs : Refs ctx inputWidth) (remaining : Nat) : Circuit ctx ctx :=
  .iterate remaining (IntegerSqrt.roundInto (wideInput refs) refs.round)

/-- The actual final store and chronological vector of selected round paths. -/
def roundsStep (refs : Refs ctx inputWidth) (remaining : Nat) (store : Store ctx) :
    Store ctx × (roundsInto refs remaining).Path :=
  let advance := fun before => (IntegerSqrt.roundStep (wideInput refs) refs.round before).1
  (advance^[remaining] store,
    fun index => (IntegerSqrt.roundStep (wideInput refs) refs.round
      (advance^[index.val] store)).2)

/-- Zero refinement rounds preserve the complete input store. -/
theorem roundsStep_zero_store (refs : Refs ctx inputWidth) (store : Store ctx) :
    (roundsStep refs 0 store).1 = store := rfl

/-- One successor iteration executes its actual head round before the remaining rounds. -/
theorem roundsStep_succ_store (refs : Refs ctx inputWidth) (remaining : Nat)
    (store : Store ctx) :
    (roundsStep refs (remaining + 1) store).1 =
      (roundsStep refs remaining (IntegerSqrt.roundStep (wideInput refs) refs.round store).1).1 :=
  Function.iterate_succ_apply _ _ _

/-- The finite actual loop preserves all incoming histories and quantum-reference blocks. -/
theorem roundsInto_execute (refs : Refs ctx inputWidth) (remaining : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (roundsInto refs remaining).execute Reference state = state.mapClassical (fun entry =>
      ((roundsStep refs remaining entry.1).1,
        (entry.2, (roundsStep refs remaining entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical (IntegerSqrt.roundInto (wideInput refs) refs.round)
    (IntegerSqrt.roundStep (wideInput refs) refs.round)
    (IntegerSqrt.roundInto_execute (wideInput refs) refs.round) remaining Reference state).trans ?_
  dsimp only [roundsStep]
  exact roundsMapClassical_decision _ _ _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
