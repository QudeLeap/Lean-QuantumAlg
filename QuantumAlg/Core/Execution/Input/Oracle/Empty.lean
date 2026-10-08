/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete inputs for an empty classical service

Attaching the unique empty service state preserves every caller block and its
quantum-reference correlations. This constructs a mathematical input, without
performing a runtime operation or initializing a nonempty service.
-/

namespace QuantumAlg.Execution.OracleInput

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}

/-- Supply the unique service state while preserving an arbitrary normalized caller input. -/
public def withEmptyService (input : Input ctx Reference) :
    OracleInput ClassicalOracleModel.empty ctx Reference := by
  let update : Store ctx → Store ctx × ClassicalOracleModel.empty.HiddenState :=
    fun stored => (stored, ())
  let decision : DecidableEq (Store ctx × ClassicalOracleModel.empty.HiddenState) :=
    Classical.decEq _
  let lifted : ExecutionState (Store ctx × ClassicalOracleModel.empty.HiddenState)
      (Register.prod ctx.register Reference) :=
    @ExecutionState.mapClassical _ _ _ _ _ decision input.state update
  refine { state := lifted, normalized := ?_ }
  change lifted.mass = 1
  exact (@ExecutionState.mapClassical_mass _ _ _ _ _ decision input.state update).trans
    input.normalized

/-- Projecting away the empty service recovers the entire original caller state. -/
public theorem oracleInput_withEmptyService_caller_state (input : Input ctx Reference) :
    (withEmptyService input).caller.state = input.state := by
  dsimp only [caller, withEmptyService]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  exact ExecutionState.mapClassical_id input.state

/-- The unique empty service can also be recovered from any complete incoming input. -/
public theorem oracleInput_empty_caller_withEmptyService_state
    (input : OracleInput ClassicalOracleModel.empty ctx Reference) :
    (withEmptyService input.caller).state = input.state := by
  dsimp only [withEmptyService, caller]
  rw [ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)]
  refine (ExecutionState.executionState_mapClassical_congr input.state ?_).trans
    (ExecutionState.mapClassical_id input.state)
  funext entry
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim (() : Unit) (show Unit from entry.2)

end

end QuantumAlg.Execution.OracleInput
