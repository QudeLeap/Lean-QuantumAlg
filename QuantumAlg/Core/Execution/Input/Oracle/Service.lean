/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle.Composition
public import QuantumAlg.Core.Execution.Input.Oracle.Reference
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Initial projections of independently granted services

The closed service join selects the existing hidden-state component. Summing
the other component retains all correlations among the selected service,
caller storage, quantum systems and external reference. The projection is an
observation of the actual initial state, not a resampling or a product-state
assumption [dW19, qcnotes.tex:5381,5394].
-/

namespace QuantumAlg.ClassicalOracleModel.ServiceJoin

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {left right parent : ClassicalOracleModel}
  (join : ServiceJoin left right parent)
  {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}

/-- Selecting the left service's existing hidden state retains normalization. -/
public lemma serviceJoin_leftInput_normalized (input : OracleInput parent ctx Reference) :
    (input.state.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).1))).IsNormalized :=
  (ExecutionState.mapClassical_mass _ _).trans input.normalized

/-- Selecting the right service's existing hidden state retains normalization. -/
public lemma serviceJoin_rightInput_normalized (input : OracleInput parent ctx Reference) :
    (input.state.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).2))).IsNormalized :=
  (ExecutionState.mapClassical_mass _ _).trans input.normalized

/-- Select the existing left hidden state without changing the caller or sampling a service. -/
@[expose] public def leftInput (input : OracleInput parent ctx Reference) :
    OracleInput left ctx Reference where
  state := input.state.mapClassical fun entry => (entry.1, (join.hidden entry.2).1)
  normalized := serviceJoin_leftInput_normalized join input

/-- Select the existing right hidden state with its original caller and reference correlations. -/
@[expose] public def rightInput (input : OracleInput parent ctx Reference) :
    OracleInput right ctx Reference where
  state := input.state.mapClassical fun entry => (entry.1, (join.hidden entry.2).2)
  normalized := serviceJoin_rightInput_normalized join input

private lemma left_caller (input : OracleInput parent ctx Reference) :
    (join.leftInput input).caller.state = input.caller.state := by
  change (input.state.mapClassical
    (fun entry => (entry.1, (join.hidden entry.2).1))).mapClassical Prod.fst =
      input.state.mapClassical Prod.fst
  rw [ExecutionState.executionState_mapClassical_comp]
  rfl

/-- The left service projection retains the caller's complete quantum-reference state. -/
public lemma serviceJoin_leftInput_caller_state (input : OracleInput parent ctx Reference) :
    (join.leftInput input).caller.state = input.caller.state := left_caller join input

private lemma right_caller (input : OracleInput parent ctx Reference) :
    (join.rightInput input).caller.state = input.caller.state := by
  change (input.state.mapClassical
    (fun entry => (entry.1, (join.hidden entry.2).2))).mapClassical Prod.fst =
      input.state.mapClassical Prod.fst
  rw [ExecutionState.executionState_mapClassical_comp]
  rfl

/-- The right service projection retains the caller's complete quantum-reference state. -/
public lemma serviceJoin_rightInput_caller_state (input : OracleInput parent ctx Reference) :
    (join.rightInput input).caller.state = input.caller.state := right_caller join input

private lemma left_local (input : OracleInput parent ctx Reference) :
    (join.leftInput input).localState = input.localState.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).1)) :=
  ExecutionState.executionState_marginalLeft_mapClassical input.state _

/-- Left initialization sees the original local joint distribution under the exact projection. -/
public lemma serviceJoin_leftInput_localState (input : OracleInput parent ctx Reference) :
    (join.leftInput input).localState = input.localState.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).1)) := left_local join input

private lemma right_local (input : OracleInput parent ctx Reference) :
    (join.rightInput input).localState = input.localState.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).2)) :=
  ExecutionState.executionState_marginalLeft_mapClassical input.state _

/-- Right initialization sees the original local joint distribution under the exact projection. -/
public lemma serviceJoin_rightInput_localState (input : OracleInput parent ctx Reference) :
    (join.rightInput input).localState = input.localState.mapClassical
      (fun entry => (entry.1, (join.hidden entry.2).2)) := right_local join input

end

end QuantumAlg.ClassicalOracleModel.ServiceJoin
