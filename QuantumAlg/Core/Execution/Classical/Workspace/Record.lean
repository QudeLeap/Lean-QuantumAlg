/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Store
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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Record the actual workspace push, proved body update and matching pop. -/
public def workspaceRecord (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path) (store : Store ctx) :
    Store ctx × (Circuit.workspace ctx key shape fresh body).Path :=
  let selected := update (store.pushWorkspace key shape fresh)
  (Store.popWorkspace key shape fresh selected.1, selected.2)

/-- A proved actual body equation gives the full CQ record of its real lexical workspace. -/
public theorem execute_workspaceRecord (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys)
    (body : Circuit (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (update : Store (ctx.addWorkspace key shape fresh) →
      Store (ctx.addWorkspace key shape fresh) × body.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference History),
      letI : DecidableEq (Store (ctx.addWorkspace key shape fresh)) := Classical.decEq _
      letI : DecidableEq History := Classical.decEq _
      letI : DecidableEq body.Path := Classical.decEq _
      body.execute Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2, (update entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    letI : DecidableEq (Store ctx) := Classical.decEq _
    letI : DecidableEq History := Classical.decEq _
    letI : DecidableEq (Circuit.workspace ctx key shape fresh body).Path := Classical.decEq _
    (Circuit.workspace ctx key shape fresh body).execute Reference state =
      state.mapClassical (fun entry =>
        ((workspaceRecord key shape fresh body update entry.1).1,
          (entry.2, (workspaceRecord key shape fresh body update entry.1).2))) := by
  refine (Circuit.execute_workspace_mapClassical key shape fresh body update
    equation Reference state).trans ?_
  dsimp only [workspaceRecord]

end

end QuantumAlg.Circuit
