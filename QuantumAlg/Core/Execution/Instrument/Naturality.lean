/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Basic
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Reference naturality through the actual sequential and classical scope syntax
Only the real interpreter, record reassociation and lexical Store push/pop
are used. Every original hidden state, retained path and overwritten Store
fiber remains in the resulting state equality.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument

attribute [local instance] Classical.decEq

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

/-- The actual program commutes with every unitary on its arbitrary untouched reference. -/
@[expose] public def ReferenceNatural (code : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment) : Prop :=
  ∀ (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    code.execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      (code.execute environment Reference state).applyUnitary (fun _ =>
        UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)
private lemma classical_unitary {C D : Type} [Fintype C] [Fintype D] {R : Register}
    {first second : DecidableEq D} (state : ExecutionState C R) (update : C → D)
    (operator : UnitaryOperator R) :
    @ExecutionState.mapClassical C D _ _ R first
        (state.applyUnitary (fun _ => operator)) update =
      (@ExecutionState.mapClassical C D _ _ R second state update).applyUnitary
        (fun _ => operator) := by
  let : DecidableEq D := first
  exact (ExecutionState.applyUnitary_mapClassical state update (fun _ => operator)).symm.trans
    (congrArg (fun current : ExecutionState D R =>
      current.applyUnitary (fun _ => operator))
        (ExecutionState.executionState_mapClassical_congr state rfl))

/-- Real sequential execution preserves naturality and both actual chronological paths. -/
lemma ReferenceNatural.seq
    {first second : Circuit (.quantum gates oracles operations services)
  ctx ctx allowAllocation}
    {environment : (ExecutionModel.quantum gates oracles operations services).Environment}
    (head : ReferenceNatural first environment) (tail : ReferenceNatural second environment) :
    ReferenceNatural (first.seq second) environment := by
  intro Reference operator History _ state
  rw [Circuit.execute_seq, Circuit.execute_seq, head Reference operator]
  have secondLaw := tail Reference operator (first.execute environment Reference state)
  refine (congrArg (fun current : State ctx Reference
      (services.HiddenState × ((History × first.Path) × second.Path)) =>
    current.mapHistory (fun history =>
      (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))) secondLaw).trans ?_
  dsimp only [State.mapHistory]
  exact classical_unitary _ _ _

/-- Real identity embedding only reassociates the same child path into its actual parent path. -/
lemma ReferenceNatural.embed_identity
    {code : Circuit (.quantum gates oracles operations services)
  ctx ctx false}
    {environment : (ExecutionModel.quantum gates oracles operations
      services).Environment} (actual : ReferenceNatural code environment) :
    ReferenceNatural (Circuit.embed (allowAllocation := true) (ContextEmbedding.identity _) code)
      environment := by
  intro Reference operator History _ state
  rw [Circuit.execute_identity_embed, Circuit.execute_identity_embed, actual Reference operator]
  rfl

/-- The real lexical Store allocation preserves its body's exact unitary naturality law. -/
lemma workspace_unitary
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true)
    (Reference : Register) (operator : UnitaryOperator (ctx.register.prod Reference))
    (natural : ∀ {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) Reference
        (services.HiddenState × History)),
      body.execute environment Reference (state.applyUnitary (fun _ => operator)) =
        (body.execute environment Reference state).applyUnitary (fun _ => operator))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body).execute environment Reference
        (state.applyUnitary (fun _ => operator)) =
      ((Circuit.workspace (model := .quantum gates oracles operations services)
        ctx key shape fresh body).execute environment Reference state).applyUnitary
          (fun _ => operator) := by
  rw [Circuit.execute_workspace, Circuit.execute_workspace]
  have pushed : State.pushWorkspace
      (ctx := ctx) (Reference := Reference)
      (state.applyUnitary (fun _ => operator)) key shape fresh =
      (state.pushWorkspace key shape fresh).applyUnitary (fun _ => operator) := by
    dsimp only [State.pushWorkspace]
    exact classical_unitary state
      (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2)) operator
  rw [pushed, natural]
  dsimp only [State.popWorkspace]
  exact classical_unitary
    (body.execute environment Reference (state.pushWorkspace key shape fresh))
    (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2)) operator

/-- The actual classical lexical workspace retains reference naturality of its real body. -/
lemma ReferenceNatural.workspace (environment : (ExecutionModel.quantum gates oracles operations
  services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh)
      (ctx.addWorkspace key shape fresh) true)
    (actual : ReferenceNatural body environment) :
    ReferenceNatural (Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body) environment := by
  intro Reference operator History _ state
  exact workspace_unitary environment key shape fresh body Reference
    (UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)
    (fun {history} _ current => actual Reference operator current) state

end

end QuantumAlg.Execution
