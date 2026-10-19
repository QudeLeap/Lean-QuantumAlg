/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store.Read
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Exact deterministic execution through lexical classical workspace

These laws describe the existing workspace instruction: initialize its exact
head cell, execute its actual body and pop that same cell. Every complete
quantum-reference block and the body's real finite path are retained. No
alternative instruction language or independently chosen execution is added.
-/

namespace QuantumAlg.Execution.Store

/-- Newly allocated lexical storage contains the shape's canonical initial value. -/
lemma read_pushWorkspace_head {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    (store.pushWorkspace key shape fresh).read
      (.storage (CStorageRef.workspaceHead ctx key shape fresh)) =
      CShape.initialValue shape := rfl

/-- Entering the lexical scope preserves every structural read from its parent context. -/
lemma read_pushWorkspace_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (store : Store ctx) (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {observed : CShape} (input : CInputRef ctx observed) :
    (store.pushWorkspace key shape fresh).read (input.underWorkspace key shape fresh) =
      store.read input := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

/-- Popping the exact lexical head exposes the existing tail values without changing them. -/
lemma read_popWorkspace_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (store : Store (ctx.addWorkspace key shape fresh))
    {observed : CShape} (input : CInputRef ctx observed) :
    (Store.popWorkspace key shape fresh store).read input =
      store.read (input.underWorkspace key shape fresh) := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

end QuantumAlg.Execution.Store

namespace QuantumAlg.CInputRef

/-- The lexical lift keeps precisely the same structural read support. -/
lemma storageKeys_underWorkspace {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape)
    (key : StorageKey) (workspaceShape : CShape) (fresh : key ∉ ctx.keys) :
    (input.underWorkspace key workspaceShape fresh).storageKeys = input.storageKeys := by
  induction input with
  | storage ref => rfl
  | product left right leftIH rightIH => exact congrArg₂ List.append leftIH rightIH
  | fixedVector entries entriesIH =>
      exact congrArg List.flatten (congrArg List.ofFn (funext entriesIH))
  | first input ih => exact ih
  | second input ih => exact ih
  | vectorGet input index ih => exact ih
  | bitsGet input index ih => exact ih
  | wordBitGet input index ih => exact ih

end QuantumAlg.CInputRef

namespace QuantumAlg.Execution.State

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Workspace entry is the same typed store map on the unchanged complete quantum register. -/
lemma state_pushWorkspace_as_mapClassical {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (state.pushWorkspace key shape fresh :
        ExecutionState (Store (ctx.addWorkspace key shape fresh) × History)
          (Register.prod ctx.register Reference)) =
      state.mapClassical (fun entry =>
        (entry.1.pushWorkspace key shape fresh, entry.2)) := by
  unfold State.pushWorkspace
  congr 1

/-- Workspace exit maps its actual extended store on that same complete quantum register. -/
lemma state_popWorkspace_as_mapClassical {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (ctx.addWorkspace key shape fresh) Reference History) :
    State.popWorkspace key shape fresh state =
      ExecutionState.mapClassical (R := Register.prod ctx.register Reference) state
        (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2)) := by
  unfold State.popWorkspace
  congr 1

/-- A store update inside the scope uses the unchanged parent quantum register as its carrier. -/
lemma state_workspace_mapClassical_as_parent {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (Reference : Register) {History Later : Type} [Fintype History] [Fintype Later]
    (state : State (ctx.addWorkspace key shape fresh) Reference History)
    (update : Store (ctx.addWorkspace key shape fresh) × History →
      Store (ctx.addWorkspace key shape fresh) × Later) :
    (state.mapClassical update :
        ExecutionState (Store (ctx.addWorkspace key shape fresh) × Later)
          (Register.prod ctx.register Reference)) =
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
        (Classical.decEq (Store (ctx.addWorkspace key shape fresh) × Later)) state update := by
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Execution.State

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma mapClassical_canonicalDecision {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (decision : DecidableEq D) (state : ExecutionState C R) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ R decision state update =
      @ExecutionState.mapClassical C D _ _ R (Classical.decEq D) state update :=
  congrArg (fun selected => @ExecutionState.mapClassical C D _ _ R selected state update)
    (Subsingleton.elim decision (Classical.decEq D))

/-- The existing workspace instruction performs its actual allocation, body and release. -/
lemma execute_workspace {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (environment : model.Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.workspace ctx key shape fresh body).execute environment Reference state =
      State.popWorkspace key shape fresh
        (body.execute environment Reference (state.pushWorkspace key shape fresh)) := rfl

/-- A proved deterministic body retains its service update across lexical storage release. -/
lemma execute_workspace_mapClassical {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (environment : model.Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit model (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (step : Store (ctx.addWorkspace key shape fresh) × model.HiddenState →
      (Store (ctx.addWorkspace key shape fresh) × model.HiddenState) × body.Path)
    (bodyEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference (model.HiddenState × History)),
      body.execute environment Reference state = state.mapClassical (fun entry =>
        let result := step (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (Circuit.workspace ctx key shape fresh body).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := step (entry.1.pushWorkspace key shape fresh, entry.2.1)
        (Store.popWorkspace key shape fresh result.1.1,
          (result.1.2, (entry.2.2, result.2)))) := by
  rw [execute_workspace, bodyEquation]
  dsimp only [State.popWorkspace, State.pushWorkspace]
  erw [ExecutionState.executionState_mapClassical_comp_instances
      (R := Register.prod ctx.register Reference) (result := inferInstance),
    ExecutionState.executionState_mapClassical_comp_instances
      (R := Register.prod ctx.register Reference) (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Circuit
