/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.FailureLoop
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Induction
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Original flag observations through the actual feedback allocation and release

Actual push and pop transport the same original Boolean read. In particular,
the real release sums every feedback value while retaining its probability,
the incoming hidden state, chronological Path and arbitrary Reference.
The allocator induction below uses the actual body and fresh frame, rather
than a second program or an empty-scratch state assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private def flagInputRead {ctx : RuntimeCtx .quantum} (input : CInputRef ctx .bit)
    (store : Store ctx) : Bool := (store.read input).toBool

/-- Actual feedback allocation leaves the transported original flag weight unchanged. -/
lemma feedback_push_flag_weight {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label] (state : State ctx Reference Label)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (input : CInputRef ctx .bit) (flag : Bool) :
    CheckerTail.readWeight (state.pushWorkspace key shape fresh)
        (flagInputRead (input.underWorkspace key shape fresh)) flag =
      CheckerTail.readWeight state (flagInputRead input) flag := by
  change ExecutionState.effectWeight (R := ctx.register.prod Reference)
      (state.pushWorkspace key shape fresh)
      (fun entry => flagEffect (ctx.register.prod Reference)
        (entry.1.read (input.underWorkspace key shape fresh)).toBool flag) =
    state.effectWeight (fun entry => flagEffect (ctx.register.prod Reference)
      (entry.1.read input).toBool flag)
  rw [State.state_pushWorkspace_as_mapClassical]
  rw [ExecutionState.effectWeight_mapClassical_decision]
  simp only [Store.read_pushWorkspace_underWorkspace]

/-- Actual feedback release combines its real fibers and retains the original flag weight. -/
lemma feedback_pop_flag_weight {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label]
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (state : State (ctx.addWorkspace key shape fresh) Reference Label)
    (input : CInputRef ctx .bit) (flag : Bool) :
    CheckerTail.readWeight (State.popWorkspace key shape fresh state)
        (flagInputRead input) flag =
      CheckerTail.readWeight state
        (flagInputRead (input.underWorkspace key shape fresh)) flag := by
  change ExecutionState.effectWeight
      (R := (ctx.addWorkspace key shape fresh).register.prod Reference)
      (State.popWorkspace (ctx := ctx) key shape fresh state)
      (fun entry => flagEffect ((ctx.addWorkspace key shape fresh).register.prod Reference)
        (entry.1.read input).toBool flag) =
    state.effectWeight
      (fun entry => flagEffect ((ctx.addWorkspace key shape fresh).register.prod Reference)
        (entry.1.read (input.underWorkspace key shape fresh)).toBool flag)
  unfold State.popWorkspace
  rw [ExecutionState.effectWeight_mapClassical_decision]
  simp only [Store.read_popWorkspace_underWorkspace]

private def PreservesFlagWeight {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (input : CInputRef ctx .bit) (flag : Bool)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    CheckerTail.readWeight (code.execute environment Reference state) (flagInputRead input) flag =
      CheckerTail.readWeight state (flagInputRead input) flag

private lemma workspace_preserves_flag_weight {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (input : CInputRef ctx .bit) (flag : Bool)
    (bodyEquation : PreservesFlagWeight (input.underWorkspace key shape fresh)
      flag body environment) :
    PreservesFlagWeight input flag (Circuit.workspace
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx key shape fresh body) environment := by
  intro Reference History _ state
  rw [Circuit.execute_workspace, feedback_pop_flag_weight]
  exact (bodyEquation (state.pushWorkspace key shape fresh)).trans
    (feedback_push_flag_weight state key shape fresh input flag)

/-- The original actual lexical frame transports a proved same-body flag observation. -/
lemma withFrame_preserves_flag_weight {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (scratch : Frame inner wordWidth parityCount) → CallerFree scratch lift →
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (input : CInputRef ctx .bit) (flag : Bool)
    (bodyEquation : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (scratch : Frame inner wordWidth parityCount) (fresh : CallerFree scratch lift),
      PreservesFlagWeight (lift.liftInput input) flag
        (body lift same scratch fresh) environment) :
    PreservesFlagWeight input flag
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := by
  have actual : PreservesFlagWeight ((Transport.id ctx).liftInput input) flag
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (Transport.id ctx) rfl
    (shapes wordWidth parityCount)
    (fun cells distinct lift separated same =>
      body lift (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct lift separated))
    (fun lift _ code => PreservesFlagWeight (lift.liftInput input) flag code environment)
    (by
      intro inner lift same key shape fresh code established
      apply workspace_preserves_flag_weight key shape fresh code environment
        (lift.liftInput input) flag
      intro Reference History finite state
      have returned := @established Reference History finite state
      simpa only [Transport.liftInput_underWorkspace] using returned)
    (by
      intro inner cells distinct lift separated same Reference History finite state
      exact @bodyEquation inner lift (quantumLayout_wires_of_quantumWires same)
        (Frame.ofCells cells distinct) (ofCells_callerFree cells distinct lift separated)
        Reference History finite state)
  intro Reference History finite state
  have returned := @actual Reference History finite state
  simpa only [Transport.liftInput_id] using returned

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
