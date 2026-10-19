/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input.Oracle.Embedding
public import QuantumAlg.Core.Execution.State.Marginal.Coordinates
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Reference-independent admission at a physical placement

The local problem sees the physical subsystem marginal of the original caller
and the original service labels. These observations are functions of the local
input alone, so arbitrary admissibility predicates apply to every external
reference extension without conditioning on the complement's classical value
[dW19, qcnotes.tex:5381,5394,6827].
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)
  {C D E : Type} [Fintype C] [Fintype D] [Fintype E]

/-- Observe the placed subsystem and the specified original classical labels. -/
public def projectLocal (state : ExecutionState C caller.register) (read : C → D) :
    ExecutionState D localCtx.register :=
  ((state.reindex (S := localCtx.register.prod placement.frame.register)
    placement.basis).marginalLeft).mapClassical read

/-- Forgetting the complement preserves the complete probability mass. -/
public lemma contextEmbedding_projectLocal_mass
    (state : ExecutionState C caller.register) (read : C → D) :
    (placement.projectLocal state read).mass = state.mass := by
  rw [projectLocal, ExecutionState.mapClassical_mass,
    ExecutionState.executionState_marginalLeft_mass, ExecutionState.reindex_mass]

/-- Successive classical observations read the same original labels. -/
public lemma contextEmbedding_projectLocal_mapClassical
    (state : ExecutionState C caller.register) (first : C → D) (second : D → E) :
    (placement.projectLocal state first).mapClassical second =
      placement.projectLocal state (second ∘ first) := by
  rw [projectLocal, ExecutionState.executionState_mapClassical_comp]
  rfl

private lemma reference_marginal {Reference : Register}
    (state : ExecutionState C (caller.register.prod Reference)) :
    (state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).marginalLeft =
      (state.marginalLeft.reindex (S := localCtx.register.prod placement.frame.register)
        placement.basis).marginalLeft := by
  rw [referenceBasis, ← ExecutionState.reindex_trans
    (S := (localCtx.register.prod placement.frame.register).prod Reference),
    ExecutionState.executionState_marginalLeft_reindex_assoc,
    ExecutionState.executionState_marginalLeft_reindex_local]

private lemma framed_local_state {oracles : ClassicalOracleModel} {Reference : Register}
    (input : OracleInput oracles caller Reference) :
    (placement.framedInput input).localState =
      placement.projectLocal input.localState
        (fun label => ((placement.store label.1).1, label.2)) := by
  change (placement.framedInput input).state.marginalLeft =
    placement.projectLocal input.state.marginalLeft
      (fun label => ((placement.store label.1).1, label.2))
  simp only [framedInput, split, projectLocal]
  rw [ExecutionState.executionState_marginalLeft_mapClassical, reference_marginal,
    ExecutionState.executionState_marginalLeft_mapClassical,
    ← ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_marginalLeft_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Local initialization is the unconditioned physical projection of the original joint input. -/
public lemma contextEmbedding_framedInput_localState
    {oracles : ClassicalOracleModel} {Reference : Register}
    (input : OracleInput oracles caller Reference) :
    (placement.framedInput input).localState =
      placement.projectLocal input.localState
        (fun label => ((placement.store label.1).1, label.2)) :=
  framed_local_state placement input

private lemma framed_caller_local_state {oracles : ClassicalOracleModel} {Reference : Register}
    (input : OracleInput oracles caller Reference) :
    (placement.framedInput input).caller.localState =
      placement.projectLocal input.caller.localState
        (fun store => (placement.store store).1) := by
  change ((placement.framedInput input).state.mapClassical Prod.fst).marginalLeft = _
  rw [ExecutionState.executionState_marginalLeft_mapClassical]
  change (placement.framedInput input).localState.mapClassical Prod.fst = _
  rw [contextEmbedding_framedInput_localState,
    contextEmbedding_projectLocal_mapClassical]
  change _ = placement.projectLocal
    ((input.state.mapClassical Prod.fst).marginalLeft) _
  rw [ExecutionState.executionState_marginalLeft_mapClassical]
  simp only [projectLocal]
  rw [← ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_marginalLeft_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  rfl

/-- Local caller validity observes the same physical projection for every reference extension. -/
public lemma contextEmbedding_framedInput_caller_localState
    {oracles : ClassicalOracleModel} {Reference : Register}
    (input : OracleInput oracles caller Reference) :
    (placement.framedInput input).caller.localState =
      placement.projectLocal input.caller.localState
        (fun store => (placement.store store).1) :=
  framed_caller_local_state placement input

end

end QuantumAlg.ContextEmbedding
