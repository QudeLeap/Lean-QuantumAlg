/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Exact records of the existing lexical workspace instruction

The record is the actual store push, supplied body record and matching pop.
Its theorem requires a proof of the real body's interpreter equation and
preserves the full Store-history and quantum-reference state. Instantiating
this abstract carrier avoids repeatedly expanding a large body's finite path
when composing concrete nested scopes. No additional interpreter is defined.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

/-- Record the actual workspace push, proved body transition and matching store pop. -/
public def workspaceRecord (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) × model.HiddenState →
      (Store (ctx.addWorkspace key shape fresh) × model.HiddenState) × body.Path)
    (entry : Store ctx × model.HiddenState) :
    (Store ctx × model.HiddenState) × (Circuit.workspace ctx key shape fresh body).Path :=
  let selected := update (entry.1.pushWorkspace key shape fresh, entry.2)
  ((Store.popWorkspace key shape fresh selected.1.1, selected.1.2), selected.2)

open scoped Classical in
/-- A proved actual body equation gives the full CQ record of its real lexical workspace. -/
public lemma execute_workspaceRecord
    (environment : model.Environment) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) × model.HiddenState →
      (Store (ctx.addWorkspace key shape fresh) × model.HiddenState) × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := update (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.workspace ctx key shape fresh body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := workspaceRecord key shape fresh body update (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  refine (Circuit.execute_workspace_mapClassical environment key shape fresh body update
    ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (equation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Record a lexical caller-store update whose body leaves service state unchanged. -/
public def workspaceStoreRecord (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path) (store : Store ctx) :
    Store ctx × (Circuit.workspace ctx key shape fresh body).Path :=
  let result := update (store.pushWorkspace key shape fresh)
  (Store.popWorkspace key shape fresh result.1, result.2)

open scoped Classical in
/-- A store-only body equation lifts through lexical storage and persistent service state. -/
public lemma execute_workspaceStoreRecord
    (environment : model.Environment) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := update entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.workspace ctx key shape fresh body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := workspaceStoreRecord key shape fresh body update entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  refine (execute_workspaceRecord environment key shape fresh body
    (preserveHiddenRecord (model := model) update) ?_ Reference state).trans ?_
  · intro reference history _ input
    exact (equation reference input).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)
  · exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Circuit
