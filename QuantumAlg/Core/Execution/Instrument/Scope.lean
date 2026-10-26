/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Retained Kraus records through the actual classical workspace instruction

The child is the fixed actual Circuit. Its original Store is initialized by
the real workspace push and its returned Store is released by the matching
pop. Every operator acts on the unchanged complete quantum register; hidden
state, chronological Path and incoming history remain in the same fibers.
No quantum state is allocated, replaced or conditioned on an arithmetic law.
-/

public section

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

private lemma retained_blocks_push {Original Intermediate Outcome Result : Type}
    [Fintype Original] [Fintype Intermediate] [Fintype Outcome]
    [DecidableEq Intermediate] [DecidableEq Result] {R : Register}
    (state : ExecutionState Original R) (push : Original → Intermediate)
    (record : Intermediate → Outcome → Result)
    (operators : Intermediate → Outcome → HilbertOperator R) (result : Result) :
    (∑ middle : Intermediate, ∑ outcome : Outcome,
      if record middle outcome = result then
        operators middle outcome * ((state.mapClassical push).block middle).matrix *
          (operators middle outcome).conjTranspose else 0) =
      ∑ original : Original, ∑ outcome : Outcome,
        if record (push original) outcome = result then
          operators (push original) outcome * (state.block original).matrix *
            (operators (push original) outcome).conjTranspose else 0 := by
  simp_rw [ExecutionState.mapClassical_block_matrix]
  simpa only [Fintype.sum_unique] using
    composeRetainedBlocks (fun original (_ : Unit) => push original) record
      (fun original _ => (state.block original).matrix) operators result

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Outcome : Type} [Fintype Outcome]
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- Actual workspace entry, actual child records and actual exit determine the same Kraus rows. -/
def Instrument.workspace (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : Instrument body Outcome environment) :
    Instrument (Circuit.workspace
      (model := .quantum gates oracles operations services)
      ctx key shape fresh body) Outcome environment where
  record store outcome :=
    let next := actual.record (store.pushWorkspace key shape fresh) outcome
    (Store.popWorkspace key shape fresh next.1, next.2)
  operator store outcome := actual.operator (store.pushWorkspace key shape fresh) outcome
  blocks := by
    intro Reference History _ state result
    let pushed := state.pushWorkspace key shape fresh
    let finished := body.execute environment Reference pushed
    let pop := fun entry : Store (ctx.addWorkspace key shape fresh) ×
        (services.HiddenState × (History × body.Path)) =>
      (Store.popWorkspace key shape fresh entry.1, entry.2)
    have execution :
        (Circuit.workspace (model := .quantum gates oracles operations services)
          ctx key shape fresh body).execute environment Reference state =
          finished.mapClassical pop := by
      rw [Circuit.execute_workspace]
      exact (State.state_popWorkspace_as_mapClassical key shape fresh Reference finished).trans
        (ExecutionState.executionState_mapClassical_congr finished rfl)
    refine (congrArg (fun output : State ctx Reference
      (services.HiddenState × (History × body.Path)) => (output.block result).matrix)
        execution).trans ?_
    have remapped := mapClassical_retained_matrix finished
      (retainedRecord (services := services) actual.record)
      (fun original outcome => referenceLift Reference (actual.operator original.1 outcome) *
        (pushed.block original).matrix *
          (referenceLift Reference (actual.operator original.1 outcome)).conjTranspose)
      (by
        intro selected
        exact (actual.blocks Reference pushed selected).trans
          (sum_condition_decisions _ _ _ _)) pop result
    refine remapped.trans ?_
    have pushedMap : (pushed : ExecutionState
        (Store (ctx.addWorkspace key shape fresh) × (services.HiddenState × History))
        (ctx.register.prod Reference)) =
      state.mapClassical (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2)) :=
      (State.state_pushWorkspace_as_mapClassical key shape fresh Reference state).trans
        (ExecutionState.executionState_mapClassical_congr state rfl)
    rw [pushedMap]
    exact retained_blocks_push state
      (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2))
      (fun entry outcome => pop (retainedRecord (services := services) actual.record entry outcome))
      (fun entry outcome => referenceLift Reference (actual.operator entry.1 outcome)) result

end

end QuantumAlg.Execution
