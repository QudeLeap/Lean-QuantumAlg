/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Composition.Parallel
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Composition.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Arbitrary history maps through complete physical and service composition

The equalities concern complete density blocks, including noninjective history
maps. Complement stores and inactive service states remain separate from the
history being changed. No independence assumption is imposed on the input.
-/

namespace QuantumAlg

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution.State

private lemma composition_mapHistory_comp {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} {H K L : Type} [Fintype H] [Fintype K] [Fintype L]
    (state : State ctx Reference H) (first : H → K) (second : K → L) :
    (state.mapHistory first).mapHistory second = state.mapHistory (second ∘ first) := by
  simp only [mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]

end Execution.State

namespace ContextEmbedding

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference : Register}
  {H K : Type} [Fintype H] [Fintype K]

/-- Splitting retains the complement store while mapping an arbitrary external history. -/
lemma split_mapHistory (state : State caller Reference H) (update : H → K) :
    placement.split (state.mapHistory update) =
      (placement.split state).mapHistory (fun record => (record.1, update record.2)) := by
  unfold split State.mapHistory
  rw [ExecutionState.composition_reindex_mapClassical _ _ _ _ (Classical.decEq _)]
  simp only [ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun current : ExecutionState
    (Store localCtx × (Store placement.frame × K)) (Register.prod caller.register Reference) =>
      current.reindex (placement.referenceBasis Reference))
  exact ExecutionState.executionState_mapClassical_congr state rfl

/-- Rejoining commutes with history changes and retains the complete complement. -/
lemma join_mapHistory
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × H)) (update : H → K) :
    placement.join (state.mapHistory (fun record => (record.1, update record.2))) =
      (placement.join state).mapHistory update := by
  unfold join State.mapHistory
  rw [ExecutionState.composition_reindex_mapClassical _ _ _ _ (Classical.decEq _)]
  simp only [ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun current : ExecutionState (Store caller × K)
    (Register.prod localCtx.register (Register.prod placement.frame.register Reference)) =>
      current.reindex (placement.referenceBasis Reference).symm)
  exact ExecutionState.executionState_mapClassical_congr state rfl

end ContextEmbedding

namespace Execution

/-- Naturality of an internal recursive interpretation in its mathematical history. -/
abbrev HistoryNatural {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path] {Reference : Register}
    (body : Preserving Hidden ctx ctx Reference Path) : Prop :=
  ∀ {H K : Type} [Fintype H] [Fintype K]
    (state : State ctx Reference (Hidden × H)) (update : H → K),
    (body (state.mapHistory (fun record => (record.1, update record.2)))).val =
      (body state).val.mapHistory
        (fun record => (record.1, (update record.2.1, record.2.2)))

/-- Complete physical framing preserves arbitrary history naturality. -/
lemma embedPreserving_history {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    {Hidden Path : Type} [Fintype Hidden] [Fintype Path]
    (placement : ContextEmbedding localCtx caller) (Reference : Register)
    (body : Preserving Hidden localCtx localCtx
      (Register.prod placement.frame.register Reference) Path)
    (natural : HistoryNatural body) :
    HistoryNatural (embedPreserving placement Reference body) := by
  intro H K _ _ state update
  let localState := (placement.split state).mapHistory
    (fun history => (history.2.1, (history.1, history.2.2)))
  have input :
      (placement.split (state.mapHistory (fun record => (record.1, update record.2)))).mapHistory
          (fun history => (history.2.1, (history.1, history.2.2))) =
        localState.mapHistory
          (fun record => (record.1, (record.2.1, update record.2.2))) := by
    rw [placement.split_mapHistory]
    simp only [localState, State.composition_mapHistory_comp, Function.comp_def]
  change placement.join ((body _).val.mapHistory _) =
    (placement.join ((body localState).val.mapHistory _)).mapHistory _
  rw [input, natural localState (fun record => (record.1, update record.2)),
    ← placement.join_mapHistory]
  simp only [State.composition_mapHistory_comp, Function.comp_def]

variable {left right parent : ClassicalOracleModel}
  (join : ClassicalOracleModel.ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {Path : Type} [Fintype Path]

/-- Selecting the left service preserves every arbitrary mathematical history map. -/
lemma serviceLeftPreserving_history
    (body : Preserving left.HiddenState ctx ctx Reference Path)
    (natural : HistoryNatural body) : HistoryNatural (serviceLeftPreserving join body) := by
  intro H K _ _ state update
  have input : serviceInputLeft join
      (state.mapHistory (fun record => (record.1, update record.2))) =
      (serviceInputLeft join state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
    simp only [serviceInputLeft, State.mapHistory,
      ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr state rfl
  change serviceOutputLeft join (body _).val =
    (serviceOutputLeft join (body (serviceInputLeft join state)).val).mapHistory _
  rw [input, natural (serviceInputLeft join state)
    (fun record => (record.1, update record.2))]
  simp only [serviceOutputLeft, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Selecting the right service preserves every arbitrary mathematical history map. -/
lemma serviceRightPreserving_history
    (body : Preserving right.HiddenState ctx ctx Reference Path)
    (natural : HistoryNatural body) : HistoryNatural (serviceRightPreserving join body) := by
  intro H K _ _ state update
  have input : serviceInputRight join
      (state.mapHistory (fun record => (record.1, update record.2))) =
      (serviceInputRight join state).mapHistory
        (fun record => (record.1, (record.2.1, update record.2.2))) := by
    simp only [serviceInputRight, State.mapHistory,
      ExecutionState.executionState_mapClassical_comp]
    exact ExecutionState.executionState_mapClassical_congr state rfl
  change serviceOutputRight join (body _).val =
    (serviceOutputRight join (body (serviceInputRight join state)).val).mapHistory _
  rw [input, natural (serviceInputRight join state)
    (fun record => (record.1, update record.2))]
  simp only [serviceOutputRight, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both independent services and every complement survive an arbitrary history map. -/
lemma parallelPreserving_history {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftPath)
    (second : Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightPath)
    (firstNatural : HistoryNatural first) (secondNatural : HistoryNatural second) :
    HistoryNatural (parallelPreserving join separate first second) := by
  have leftNatural : HistoryNatural (serviceLeftPreserving join
      (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
        Reference first)) := serviceLeftPreserving_history join _
    (embedPreserving_history (ContextEmbedding.alongUnion leftCtx rightCtx separate)
      Reference first firstNatural)
  have rightNatural : HistoryNatural (serviceRightPreserving join
      (embedPreserving (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
        Reference second)) := serviceRightPreserving_history join _
    (embedPreserving_history (ContextEmbedding.alongUnionRight leftCtx rightCtx separate)
      Reference second secondNatural)
  intro H K _ _ state update
  dsimp only [parallelPreserving, embedServiceLeftPreserving, embedServiceRightPreserving]
  rw [leftNatural state update,
    rightNatural
      (serviceLeftPreserving join
        (embedPreserving (ContextEmbedding.alongUnion leftCtx rightCtx separate)
          Reference first) state).val
      (fun record : H × LeftPath => (update record.1, record.2))]
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end Execution

end

end QuantumAlg
