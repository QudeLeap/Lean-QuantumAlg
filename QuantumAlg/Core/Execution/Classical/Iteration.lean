/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Interpret
import Mathlib.Logic.Function.Iterate

/-!
# Deterministic state equations for actual circuit iteration

The existing iterate instruction repeatedly executes its actual body and
records one body path at each finite index. Given the body's proved complete
state equation, these laws identify the final store with ordinary function
iteration and each path with the update at that stage. There is no second
executor or additional instruction syntax.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Zero actual iterations preserve storage and attach the unique empty path vector. -/
theorem execute_iterate_zero (body : Circuit ctx ctx) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.iterate 0 body).execute Reference state =
      state.mapHistory (fun history => (history, Fin.elim0)) := rfl

/-- A successor iteration executes one body before the remaining actual iterations. -/
theorem execute_iterate_succ (body : Circuit ctx ctx) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.iterate (count + 1) body).execute Reference state =
      ((Circuit.iterate count body).execute Reference (body.execute Reference state)).mapHistory
        (fun history => (history.1.1, Fin.cons history.1.2 history.2)) := rfl

private theorem iteration_empty_records {A B : Type} (step : A → A × B) (input : A) :
    (Fin.elim0 : Fin 0 → B) =
      (fun index : Fin 0 => (step ((fun value => (step value).1)^[index.val] input)).2) := by
  funext index
  exact Fin.elim0 index

private theorem iteration_cons_records {A B : Type} (step : A → A × B)
    (count : Nat) (input : A) :
    Fin.cons (step input).2
      (fun index : Fin count =>
        (step ((fun value => (step value).1)^[index.val] (step input).1)).2) =
      (fun index : Fin (count + 1) =>
        (step ((fun value => (step value).1)^[index.val] input)).2) := by
  funext index
  refine Fin.cases ?_ (fun tail => ?_) index
  · rfl
  · simp only [Fin.cons_succ, Fin.val_succ, Function.iterate_succ_apply]

/-- Actual iteration keeps every quantum-reference block and records its exact stage paths. -/
theorem execute_iterate_mapClassical (body : Circuit ctx ctx)
    (step : Store ctx → Store ctx × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      body.execute Reference state = state.mapClassical (fun entry =>
        ((step entry.1).1, (entry.2, (step entry.1).2))))
    (count : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.iterate count body).execute Reference state =
      state.mapClassical (fun entry =>
        ((fun store => (step store).1)^[count] entry.1,
          (entry.2, fun index : Fin count =>
            (step ((fun store => (step store).1)^[index.val] entry.1)).2))) := by
  induction count generalizing History with
  | zero =>
      rw [execute_iterate_zero]
      simp only [State.mapHistory, Function.iterate_zero_apply]
      have records : (fun entry : Store ctx × History =>
          (entry.1, (entry.2, (Fin.elim0 : Fin 0 → body.Path)))) =
          (fun entry : Store ctx × History =>
            (entry.1, (entry.2, fun index : Fin 0 =>
              (step ((fun store => (step store).1)^[index.val] entry.1)).2))) := by
        funext entry
        exact congrArg (fun paths => (entry.1, (entry.2, paths)))
          (iteration_empty_records step entry.1)
      rw [records]
      congr 1
      exact Subsingleton.elim _ _
  | succ count ih =>
      rw [execute_iterate_succ, ih, bodyEquation]
      simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
        Function.comp_def, iteration_cons_records, Function.iterate_succ_apply]
      congr 1
      exact Subsingleton.elim _ _

end

end QuantumAlg.Circuit
