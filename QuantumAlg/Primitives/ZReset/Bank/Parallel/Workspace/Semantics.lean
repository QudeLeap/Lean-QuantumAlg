/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Scope
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Workspace.Store
import all QuantumAlg.Core.Execution.Measured.FeedForward

/-!
# Complete reset equations through actual parent workspace scopes

The proof follows the existing workspace instruction: initialize one
real classical head, execute the supplied body, and remove that head.
The matrix equation is transported for any original-store predicate,
so every arbitrary reference correlation survives each scope boundary.
-/

namespace QuantumAlg.ZReset.BankParallel

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

variable {environment : (ExecutionModel.quantum gates
  oracles operations services).Environment}

/-- The exact zero-bank equation for all input blocks selected by one store predicate. -/
def ResetEquation (environment : (ExecutionModel.quantum gates
    oracles operations services).Environment) {ctx : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation)
    (predicate : Store ctx → Prop) : Prop :=
  ∀ (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index),
    ((code.execute environment Reference state).filterClassical
      (fun entry => predicate entry.1)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0

/-- A classical map transports the block predicate and leaves full quantum coordinates intact. -/
lemma mapped_filter_entry {C D : Type} [Fintype C] [Fintype D] {R : Register}
    (decision : DecidableEq D) (state : ExecutionState C R) (update : C → D) (predicate : D → Prop)
    (left right : R.Index) :
    ((@ExecutionState.mapClassical C D _ _ R decision state update).filterClassical
      predicate).quantumMarginal.matrix left right =
      (state.filterClassical (fun entry => predicate (update entry))).quantumMarginal.matrix
        left right := by
  rw [ExecutionState.filterClassical_matrix_weighted,
    ExecutionState.weightedMatrixEntry_mapClassical,
    ExecutionState.filterClassical_matrix_weighted]

/-- A real lexical scope preserves the reset equation for the entire parent-store predicate. -/
lemma workspace_resetEquation {ctx : RuntimeCtx .quantum}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (predicate : Store ctx → Prop)
    (equation : ResetEquation environment body
      (fun store => predicate (Store.popWorkspace key shape fresh store))) :
    ResetEquation environment
      (Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body) predicate := by
  intro Reference History historyFinite state left right leftRef rightRef
  rw [Circuit.execute_workspace, State.state_popWorkspace_as_mapClassical]
  refine (mapped_filter_entry (R := Register.prod ctx.register Reference) _
    (body.execute environment Reference (state.pushWorkspace key shape fresh))
    (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2))
    (fun entry => predicate entry.1) (left, leftRef) (right, rightRef)).trans ?_
  refine (equation Reference (state.pushWorkspace key shape fresh)
    left right leftRef rightRef).trans ?_
  change (if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
    ∑ basis : ctx.register.Index,
      ((state.pushWorkspace key shape fresh).filterClassical
        (fun entry => predicate
          (Store.popWorkspace key shape fresh entry.1))).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef)
    else 0) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0
  split_ifs
  · apply Finset.sum_congr rfl
    intro basis _
    rw [State.state_pushWorkspace_as_mapClassical]
    exact mapped_filter_entry (R := Register.prod ctx.register Reference) _ state
      (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2))
      (fun entry => predicate (Store.popWorkspace key shape fresh entry.1))
      (basis, leftRef) (basis, rightRef)
  · rfl

namespace Workspace

/-- All scratch scopes transport the same complete original-store equation. -/
lemma scope_resetEquation (ctx : RuntimeCtx .quantum) (count : Nat)
    (body : Circuit (.quantum gates oracles operations services)
      (context ctx count) (context ctx count))
    (predicate : Store ctx → Prop)
    (equation : ResetEquation environment body
      (fun store => predicate (forgetStore ctx count store))) :
    ResetEquation environment (scope (model := .quantum gates oracles operations services)
      ctx count body) predicate := by
  induction count with
  | zero => exact equation
  | succ count ih =>
      apply ih
      exact workspace_resetEquation (context ctx count).canonicalFreshKey (.finite 2)
        (context ctx count).canonicalFreshKey_fresh body
        (fun store => predicate (forgetStore ctx count store)) equation

end Workspace

/-- The actual identity already satisfies the complete reset equation for an empty bank. -/
lemma identity_resetEquation_empty {ctx : RuntimeCtx .quantum}
    (empty : ctx.systemCount = 0) (predicate : Store ctx → Prop) :
    ResetEquation environment (Circuit.id (allowAllocation := allowAllocation)
      (model := .quantum gates oracles operations services) ctx) predicate := by
  intro Reference History historyFinite state left right leftRef rightRef
  have only (basis : ctx.register.Index) : basis = ctx.quantumLayout.zeroLabel := by
    funext wire
    have impossible : False := by
      have bounded := wire.isLt
      omega
    exact impossible.elim
  let : Unique ctx.register.Index := ⟨⟨ctx.quantumLayout.zeroLabel⟩, only⟩
  rw [Circuit.execute_id]
  refine (mapped_filter_entry (R := Register.prod ctx.register Reference) _ state
    (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
    (fun entry => predicate entry.1) (left, leftRef) (right, rightRef)).trans ?_
  change (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) = _
  rw [if_pos ⟨only left, only right⟩, Fintype.sum_unique, only left, only right, only default]

end

end QuantumAlg.ZReset.BankParallel
