/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Input.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# The same complete caller input through both physical projection routes

Forgetting the service before or after physical placement gives the same
normalized local Input, retaining its original external quantum reference.
State promises therefore observe exactly the input supplied to the original
child execution, without an additional initialization or admission premise.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

attribute [local instance] Classical.decEq

private lemma input_eq_of_state_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {Reference : Register} (first second : Input ctx Reference)
    (agree : first.state = second.state) : first = second := by
  cases first
  cases second
  cases agree
  rfl

/-- Caller projection commutes with physical placement on the complete normalized input. -/
lemma contextEmbedding_localInput_caller
    {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
    (placement : ContextEmbedding localCtx caller)
    {oracles : ClassicalOracleModel} {Reference : Register}
    (input : OracleInput oracles caller Reference) :
    (placement.localInput input).caller = placement.projectInput input.caller := by
  apply input_eq_of_state_eq
  dsimp only [localInput, framedInput, split, OracleInput.forgetReferenceFrame,
    OracleInput.caller, projectInput]
  simp only [← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun current : ExecutionState (Store localCtx)
      (caller.register.prod Reference) =>
    (current.reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame)
  exact ExecutionState.executionState_mapClassical_congr input.state rfl

end

end QuantumAlg.ContextEmbedding
