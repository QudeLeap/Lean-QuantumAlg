/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout

/-!
# Exact execution of the recovery field scopes

The existing workspace interpreter initializes every actual recovery head,
executes the proved body and releases those same heads. These equations are
composition lemmas about that interpreter; the body equation is discharged by
the real recovery circuit, never supplied as part of a public algorithm input.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind}

/-- The actual scope record attaches precisely the path produced by its executed body. -/
def scopeRecoveryStep (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) :
    (fields : List RecoveryField) →
    (body : Circuit (fieldsContext ctx modulusWidth candidateWidth fields)
      (fieldsContext ctx modulusWidth candidateWidth fields)) →
    (Store (fieldsContext ctx modulusWidth candidateWidth fields) →
      Store (fieldsContext ctx modulusWidth candidateWidth fields) × body.Path) →
    Store ctx → Store ctx × (scopeRecoveryFields ctx modulusWidth candidateWidth fields body).Path
  | [], _body, step, store => step store
  | field :: rest, body, step, store =>
      let advanced := scopeRecoveryStep
        (ctx.addWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
        modulusWidth candidateWidth rest body step
        (store.pushWorkspace ctx.canonicalFreshKey
          (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
      (Store.popWorkspace ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh
        advanced.1, advanced.2)

/-- Actual recovery scopes compose a proved complete-state body equation through real heads. -/
theorem nativeRecovery_scope_execute (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField)
    (body : Circuit (fieldsContext ctx modulusWidth candidateWidth fields)
      (fieldsContext ctx modulusWidth candidateWidth fields))
    (step : Store (fieldsContext ctx modulusWidth candidateWidth fields) →
      Store (fieldsContext ctx modulusWidth candidateWidth fields) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (fieldsContext ctx modulusWidth candidateWidth fields) Reference History),
      body.execute Reference state = state.mapClassical (fun entry =>
        ((step entry.1).1, (entry.2, (step entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (scopeRecoveryFields ctx modulusWidth candidateWidth fields body).execute Reference state =
      state.mapClassical (fun entry =>
        ((scopeRecoveryStep ctx modulusWidth candidateWidth fields body step entry.1).1,
          (entry.2,
            (scopeRecoveryStep ctx modulusWidth candidateWidth fields body step entry.1).2))) := by
  induction fields generalizing ctx Reference History with
  | nil => exact bodyEquation Reference state
  | cons field rest ih =>
      refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
        (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh
        (scopeRecoveryFields
          (ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest body)
        (scopeRecoveryStep
          (ctx.addWorkspace ctx.canonicalFreshKey
            (recoveryFieldShape modulusWidth candidateWidth field) ctx.canonicalFreshKey_fresh)
          modulusWidth candidateWidth rest body step)
        (fun reference {_} _ initial => ih _ body step bodyEquation reference initial)
        Reference state).trans ?_
      congr 1

/-- The actual scope output is the body's actual store between the exact enter and leave maps. -/
theorem nativeRecovery_scope_store (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField)
    (body : Circuit (fieldsContext ctx modulusWidth candidateWidth fields)
      (fieldsContext ctx modulusWidth candidateWidth fields))
    (step : Store (fieldsContext ctx modulusWidth candidateWidth fields) →
      Store (fieldsContext ctx modulusWidth candidateWidth fields) × body.Path)
    (store : Store ctx) :
    (scopeRecoveryStep ctx modulusWidth candidateWidth fields body step store).1 =
      leaveRecoveryFields ctx modulusWidth candidateWidth fields
        (step (enterRecoveryFields modulusWidth candidateWidth fields store)).1 := by
  induction fields generalizing ctx with
  | nil => rfl
  | cons field rest ih =>
      simp only [scopeRecoveryStep, enterRecoveryFields, leaveRecoveryFields, ih]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
