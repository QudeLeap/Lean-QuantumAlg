/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input.Oracle.Service
public import QuantumAlg.Core.Execution.Input.Oracle.Projection
import all QuantumAlg.Core.Execution.Input.Oracle.Service
import all QuantumAlg.Core.Execution.Input.Oracle.Projection
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Unconditional child admission with independent persistent services

Physical projection and service selection observe the same original joint
input. Neither operation conditions on a classical outcome or resamples a
service. Caller validity keeps the original quantum marginal, while service
initialization retains its original correlations with that caller.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)
  {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {Reference : Register} (input : OracleInput parent caller Reference)

private lemma projectLocal_source_map
    {C D E : Type} [Fintype C] [Fintype D] [Fintype E] [DecidableEq D]
    (state : ExecutionState C caller.register) (first : C → D) (second : D → E) :
    placement.projectLocal (state.mapClassical first) second =
      placement.projectLocal state (second ∘ first) := by
  unfold projectLocal
  rw [← ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_marginalLeft_mapClassical,
    ExecutionState.executionState_mapClassical_comp]

/-- Left-service admission retains the same original local caller marginal. -/
public lemma contextEmbedding_framedLeftInput_caller_localState :
    (placement.framedInput (join.leftInput input)).caller.localState =
      placement.projectLocal input.caller.localState
        (fun store => (placement.store store).1) := by
  rw [placement.contextEmbedding_framedInput_caller_localState]
  change placement.projectLocal (join.leftInput input).caller.state.marginalLeft _ = _
  rw [join.serviceJoin_leftInput_caller_state]
  rfl

/-- Right-service admission retains the same original local caller marginal. -/
public lemma contextEmbedding_framedRightInput_caller_localState :
    (placement.framedInput (join.rightInput input)).caller.localState =
      placement.projectLocal input.caller.localState
        (fun store => (placement.store store).1) := by
  rw [placement.contextEmbedding_framedInput_caller_localState]
  change placement.projectLocal (join.rightInput input).caller.state.marginalLeft _ = _
  rw [join.serviceJoin_rightInput_caller_state]
  rfl

/-- The left service's initialization sees its original unconditioned joint subsystem. -/
public lemma contextEmbedding_framedLeftInput_localState :
    (placement.framedInput (join.leftInput input)).localState =
      placement.projectLocal input.localState
        (fun label => ((placement.store label.1).1, (join.hidden label.2).1)) := by
  rw [placement.contextEmbedding_framedInput_localState,
    join.serviceJoin_leftInput_localState, projectLocal_source_map]
  rfl

/-- The right service's initialization sees its original unconditioned joint subsystem. -/
public lemma contextEmbedding_framedRightInput_localState :
    (placement.framedInput (join.rightInput input)).localState =
      placement.projectLocal input.localState
        (fun label => ((placement.store label.1).1, (join.hidden label.2).2)) := by
  rw [placement.contextEmbedding_framedInput_localState,
    join.serviceJoin_rightInput_localState, projectLocal_source_map]
  rfl

end

end QuantumAlg.ContextEmbedding
