/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.Marginal
import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Core.Execution.State.Marginal.Reference

/-!
# Partial trace through actual lexical classical allocation

Entering and leaving the real workspace change only its classical Store.
Consequently the same reference-partial-trace law of its actual body lifts
through that paid allocation and release, retaining every real Path. This
is a component law for actual scope consumers, with no assertion about
arithmetic correctness or preservation of bad-label addresses.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

private lemma classical_trace {C D : Type} [Fintype C] [Fintype D]
    {R Frame Reference : Register} {first second : DecidableEq D}
    (state : ExecutionState C (R.prod (Frame.prod Reference))) (update : C → D) :
    @ExecutionState.mapClassical C D _ _ (R.prod Reference) first
        state.forgetReferenceFrame update =
      (@ExecutionState.mapClassical C D _ _ (R.prod (Frame.prod Reference)) second
        state update).forgetReferenceFrame := by
  let : DecidableEq D := second
  exact (ExecutionState.executionState_mapClassical_congr state.forgetReferenceFrame rfl).trans
    (ExecutionState.forgetReferenceFrame_mapClassical state update).symm

/-- Reference partial trace is natural through the actual classical workspace instruction. -/
lemma window_source_workspace_partialTrace
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true)
    (natural : ∀ (Reference Frame : Register) {History : Type} [Fintype History]
      (state : State (ctx.addWorkspace key shape fresh) (Frame.prod Reference)
        (services.HiddenState × History)),
      body.execute environment Reference state.forgetReferenceFrame =
        (body.execute environment (Frame.prod Reference) state).forgetReferenceFrame)
    (Reference Frame : Register) {History : Type} [Fintype History]
    (state : State ctx (Frame.prod Reference) (services.HiddenState × History)) :
    (Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body).execute environment Reference
        state.forgetReferenceFrame =
      ((Circuit.workspace (model := .quantum gates oracles operations services)
      ctx key shape fresh body).execute environment
        (Frame.prod Reference) state).forgetReferenceFrame := by
  rw [Circuit.execute_workspace, Circuit.execute_workspace]
  have pushed : State.pushWorkspace
      (ctx := ctx) (Reference := Reference) state.forgetReferenceFrame key shape fresh =
      (state.pushWorkspace key shape fresh).forgetReferenceFrame := by
    dsimp only [State.pushWorkspace]
    exact classical_trace state
      (fun entry => (entry.1.pushWorkspace key shape fresh, entry.2))
  rw [pushed, natural Reference Frame]
  let result := body.execute environment (Frame.prod Reference)
    (state.pushWorkspace key shape fresh)
  dsimp only [State.popWorkspace]
  exact classical_trace result
    (fun entry => (Store.popWorkspace key shape fresh entry.1, entry.2))

/-- Actual chronological composition retains this law and both original circuit Paths. -/
lemma window_source_sequence_partialTrace {allowAllocation : Bool}
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment)
    (first second : Circuit (.quantum gates oracles operations services)
      ctx ctx allowAllocation)
    (firstNatural : ∀ (Reference Frame : Register) {History : Type} [Fintype History]
      (state : State ctx (Frame.prod Reference) (services.HiddenState × History)),
      first.execute environment Reference state.forgetReferenceFrame =
        (first.execute environment (Frame.prod Reference) state).forgetReferenceFrame)
    (secondNatural : ∀ (Reference Frame : Register) {History : Type} [Fintype History]
      (state : State ctx (Frame.prod Reference) (services.HiddenState × History)),
      second.execute environment Reference state.forgetReferenceFrame =
        (second.execute environment (Frame.prod Reference) state).forgetReferenceFrame)
    (Reference Frame : Register) {History : Type} [Fintype History]
    (state : State ctx (Frame.prod Reference) (services.HiddenState × History)) :
    (first.seq second).execute environment Reference state.forgetReferenceFrame =
      ExecutionState.forgetReferenceFrame
        ((first.seq second).execute environment (Frame.prod Reference) state) := by
  rw [Circuit.execute_seq, Circuit.execute_seq, firstNatural Reference Frame,
    secondNatural Reference Frame]
  let result := second.execute environment (Frame.prod Reference)
    (first.execute environment (Frame.prod Reference) state)
  let update : Store ctx × (services.HiddenState × ((History × first.Path) × second.Path)) →
      Store ctx × (services.HiddenState × (History × (first.Path × second.Path))) :=
    fun entry => (entry.1, (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2))))
  calc
    _ = result.forgetReferenceFrame.mapClassical update :=
      ExecutionState.executionState_mapClassical_congr _ rfl
    _ = (result.mapClassical update).forgetReferenceFrame :=
      (ExecutionState.forgetReferenceFrame_mapClassical result update).symm
    _ = _ := congrArg (ExecutionState.forgetReferenceFrame (R := ctx.register)
        (S := Frame) (T := Reference))
      (ExecutionState.executionState_mapClassical_congr result rfl)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
