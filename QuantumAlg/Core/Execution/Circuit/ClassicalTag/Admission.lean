/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Core.Execution.Reference.ClassicalTag.Marginal
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Unconditional admission for an encoded classical spectator

The encoded reference extension and the original spectator-forgotten input
have the same local caller and service state. Validity and initialization
therefore use the same unconditional input. No requirement is imposed on a
conditional tag slice, and no service state is initialized or reset.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace State

private lemma marginalLeft_map_decisions
    {C D : Type} [Fintype C] [Fintype D] {R S : Register}
    {decision : DecidableEq D} (state : ExecutionState C (R.prod S)) (read : C → D) :
    (@ExecutionState.mapClassical C D _ _ _ decision state read).marginalLeft =
      @ExecutionState.mapClassical C D _ _ _ decision state.marginalLeft read :=
  @ExecutionState.executionState_marginalLeft_mapClassical C D _ _ R S decision state read

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference Tag : Register}
  {Hidden H : Type} [Fintype Hidden] [Fintype H]

/-- The encoded service/history input has the unchanged local state with its tag forgotten. -/
lemma encodeOracleTag_marginalLeft
    (state : State ctx Reference (Hidden × (H × Tag.Index))) :
    (encodeOracleTag state).marginalLeft =
      state.marginalLeft.mapClassical
        (fun record => (record.1, (record.2.1, record.2.2.1))) := by
  rw [encodeOracleTag, encodeReferenceTag_marginalLeft]
  dsimp only [mapHistory]
  rw [marginalLeft_map_decisions,
    ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr state.marginalLeft rfl

/-- The caller observes the same local state when all mathematical history is forgotten. -/
lemma encodeOracleTag_caller_marginalLeft
    (state : State ctx Reference (Hidden × (H × Tag.Index))) :
    ((encodeOracleTag state).mapClassical Prod.fst).marginalLeft =
      state.marginalLeft.mapClassical Prod.fst := by
  rw [ExecutionState.executionState_marginalLeft_mapClassical,
    encodeOracleTag_marginalLeft, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr state.marginalLeft rfl

end State

namespace OracleInput

variable {oracles : ClassicalOracleModel} {kind : ProblemKind}
  {ctx : RuntimeCtx kind} {Reference Tag : Register}

/-- A complete normalized spectator state gives a reference extension of the same service input. -/
def fromClassicalTag
    (state : State ctx Reference (oracles.HiddenState × Tag.Index))
    (normalized : state.IsNormalized) : OracleInput oracles ctx (Tag.prod Reference) where
  state := State.encodeReferenceTag state
  normalized := (State.encodeReferenceTag_mass state).trans normalized

/-- Initialization sees the unconditional local joint state after the tag label is forgotten. -/
lemma fromClassicalTag_localState
    (state : State ctx Reference (oracles.HiddenState × Tag.Index))
    (normalized : state.IsNormalized) :
    (fromClassicalTag (oracles := oracles) state normalized).localState =
      state.marginalLeft.mapClassical (fun record => (record.1, record.2.1)) :=
  State.encodeReferenceTag_marginalLeft state

/-- Caller validity sees the same unconditional local caller state of the original input. -/
lemma fromClassicalTag_caller_localState
    (state : State ctx Reference (oracles.HiddenState × Tag.Index))
    (normalized : state.IsNormalized) :
    (fromClassicalTag (oracles := oracles) state normalized).caller.localState =
      state.marginalLeft.mapClassical Prod.fst := by
  change ((State.encodeReferenceTag state).mapClassical Prod.fst).marginalLeft = _
  rw [ExecutionState.executionState_marginalLeft_mapClassical,
    State.encodeReferenceTag_marginalLeft, ExecutionState.executionState_mapClassical_comp]
  exact ExecutionState.executionState_mapClassical_congr state.marginalLeft rfl

end OracleInput

end

end QuantumAlg.Execution
