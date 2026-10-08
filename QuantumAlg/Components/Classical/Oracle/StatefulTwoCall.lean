/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Classical.Step.Deterministic
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Input.Oracle

/-!
# Two actual calls to one persistent classical service

The service returns its current hidden bit and then flips it. Two sequential
calls share the same hidden state. Their recorded results are complementary,
the hidden bit returns to its initial value, and the second result overwrites
the same caller-visible cell. The complete state equation retains arbitrary
old history and every reference block.
-/

namespace QuantumAlg.ClassicalOracleExamples.StatefulTwoCall

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The service exposes its state transition and an explicit reset request. -/
inductive Query where
  | readFlip
  | reset
  deriving DecidableEq

/-- A declared deterministic service that reports and flips its hidden bit. -/
@[implicit_reducible] def service : ClassicalOracleModel where
  Query := Query
  Coordinate := Query
  coordinateDecidableEq := inferInstance
  HiddenState := Bool
  stateFintype := inferInstance
  inputShape _ := .bit
  outputShape _ := .bit
  transition query hidden _ := match query with
    | .readFlip => PMF.pure (!hidden, .bit hidden)
    | .reset => PMF.pure (false, .bit hidden)
  coordinate query := query

/-- Only this classical service is available to the two-call program. -/
@[implicit_reducible] def model : ExecutionModel := .classical .empty service

variable {ctx : RuntimeCtx .classical} (result : CWriteRef ctx .bit)

@[implicit_reducible] private def application : service.Application ctx where
  query := .readFlip
  input := .storage result.toCStorageRef
  output := result

@[implicit_reducible] private def resetApplication : service.Application ctx where
  query := .reset
  input := .storage result.toCStorageRef
  output := result

/-- One actual query reads and changes the shared hidden bit. -/
@[implicit_reducible] def call : Circuit model ctx ctx :=
  .classicalQuery (application result)

/-- Both queries use the same service and the same visible result cell. -/
@[implicit_reducible] def twoCalls : Circuit model ctx ctx :=
  .seq (call result) (call result)

/-- An actual granted query explicitly resets the service state to false. -/
@[implicit_reducible] def reset : Circuit model ctx ctx :=
  .classicalQuery (resetApplication result)

/-- One execution reports the old bit and keeps the flipped bit for later calls. -/
private theorem call_execute (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (Bool × H)) :
    (call result).execute Reference state = state.mapClassical (fun entry =>
      (entry.1.write result (.bit entry.2.1),
        (!entry.2.1, (entry.2.2, .bit entry.2.1)))) := by
  change queryStep (application result) state = _
  have actual := queryStep_of_pure (application result)
    (fun hidden _ => (!hidden, .bit hidden)) (by intro hidden value; rfl) state
  exact actual.trans (ExecutionState.executionState_mapClassical_congr state rfl)

/-- Reset reports the old hidden bit while setting the persistent bit to false;
every existing quantum and reference block remains in its original fiber. -/
theorem reset_execute (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (Bool × H)) :
    (reset result).execute Reference state = state.mapClassical (fun entry =>
      (entry.1.write result (.bit entry.2.1),
        (false, (entry.2.2, .bit entry.2.1)))) := by
  change queryStep (resetApplication result) state = _
  have actual := queryStep_of_pure (resetApplication result)
    (fun hidden _ => (false, .bit hidden)) (by intro hidden value; rfl) state
  exact actual.trans (ExecutionState.executionState_mapClassical_congr state rfl)

/-- The actual second call sees the first call's update, rather than a reset
or an independent draw; all complete reference blocks are pushed forward. -/
theorem twoCalls_execute (Reference : Register) {H : Type} [Fintype H]
    (state : State ctx Reference (Bool × H)) :
    (twoCalls result).execute Reference state = state.mapClassical (fun entry =>
      (((entry.1.write result (.bit entry.2.1)).write result (.bit (!entry.2.1))),
        (entry.2.1, (entry.2.2, (.bit entry.2.1, .bit (!entry.2.1)))))) := by
  unfold twoCalls
  rw [Circuit.execute_seq, call_execute, call_execute]
  simp only [State.mapHistory]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance)]
  erw [ExecutionState.executionState_mapClassical_comp_instances
    (result := inferInstance)]
  exact ExecutionState.executionState_mapClassical_congr state (by
    funext entry
    simp [Function.comp, Bool.not_not])

/-- The executed path charges exactly two service queries and no classical
operation event, independently of the two correlated results. -/
theorem twoCalls_eventTrace (path : (twoCalls result).Path) :
    (twoCalls result).eventTrace path =
      [.classicalQuery .readFlip, .classicalQuery .readFlip] := by
  rfl

/-- Reset is a distinct query event, rather than an uncharged change of the
hidden input state. -/
theorem reset_eventTrace (path : (reset result).Path) :
    (reset result).eventTrace path = [.classicalQuery .reset] := by
  rfl

/-- Initialization samples the hidden service state once as false and keeps
the complete caller and external reference correlations. -/
def initializedInput {Reference : Register} (caller : Input ctx Reference) :
    OracleInput service ctx Reference :=
  OracleInput.ofKernel caller (fun _ => PMF.pure false)

/-- The initialization has no true hidden-state block, even when the caller's
store and external quantum reference were correlated. -/
theorem initializedInput_true_block {Reference : Register}
    (caller : Input ctx Reference) (store : Store ctx) :
    ((initializedInput caller).state.block (store, true)).matrix = 0 := by
  rw [initializedInput, OracleInput.oracleInput_ofKernel_block_matrix]
  simp

end

end QuantumAlg.ClassicalOracleExamples.StatefulTwoCall
