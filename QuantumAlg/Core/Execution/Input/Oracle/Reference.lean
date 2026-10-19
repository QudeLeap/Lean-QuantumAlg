/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Input.Oracle
public import QuantumAlg.Core.Execution.State.Marginal
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input

/-!
# Reference projection preserves joint input admission

A problem observes the local caller and service state. Observing away one
external reference factor preserves both of these input predicates, without
conditioning on a classical label or assuming a product state
[dW19, qcnotes.tex:5381,5394,6827].
-/

namespace QuantumAlg.Execution.OracleInput

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {oracles : ClassicalOracleModel} {kind : ProblemKind}
  {ctx : RuntimeCtx kind} {Frame Reference : Register}

/-- Tracing a reference factor retains normalization of the complete input. -/
public lemma oracleInput_forgetReferenceFrame_normalized
    (input : OracleInput oracles ctx (Frame.prod Reference)) :
    input.state.forgetReferenceFrame.IsNormalized :=
  (ExecutionState.executionState_forgetReferenceFrame_mass input.state).trans input.normalized

/-- Observe away one external reference factor while retaining the actual service state. -/
@[expose] public def forgetReferenceFrame (input : OracleInput oracles ctx (Frame.prod Reference)) :
    OracleInput oracles ctx Reference where
  state := input.state.forgetReferenceFrame
  normalized := oracleInput_forgetReferenceFrame_normalized input

private lemma local_state (input : OracleInput oracles ctx (Frame.prod Reference)) :
    input.forgetReferenceFrame.localState = input.localState :=
  ExecutionState.executionState_forgetReferenceFrame_marginal input.state

/-- Initialization sees the same local joint state for both reference extensions. -/
public lemma oracleInput_forgetReferenceFrame_localState
    (input : OracleInput oracles ctx (Frame.prod Reference)) :
    input.forgetReferenceFrame.localState = input.localState := local_state input

private lemma caller_local_state (input : OracleInput oracles ctx (Frame.prod Reference)) :
    input.forgetReferenceFrame.caller.localState = input.caller.localState := by
  change (input.state.forgetReferenceFrame.mapClassical Prod.fst).marginalLeft =
    (input.state.mapClassical Prod.fst).marginalLeft
  rw [ExecutionState.executionState_marginalLeft_mapClassical,
    ExecutionState.executionState_marginalLeft_mapClassical,
    ExecutionState.executionState_forgetReferenceFrame_marginal]

/-- The caller's validity predicate also receives exactly the same complete local input. -/
public lemma oracleInput_forgetReferenceFrame_caller_localState
    (input : OracleInput oracles ctx (Frame.prod Reference)) :
    input.forgetReferenceFrame.caller.localState = input.caller.localState :=
  caller_local_state input

end

end QuantumAlg.Execution.OracleInput
