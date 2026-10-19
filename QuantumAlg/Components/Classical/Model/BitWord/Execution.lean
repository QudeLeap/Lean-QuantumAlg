/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Interpret
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual execution of a selected bit or word instruction

Each instruction is the existing native circuit leaf with its model-owned
token and real operand references. Its path records the computed value. Exact
execution retains the persistent service state and every prior joint block;
native event and depth are taken from that same leaf.
-/

namespace QuantumAlg.BitWord

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {execution : ExecutionModel} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {input output : CShape}

/-- One actual native leaf, admitted by the surrounding selection. -/
@[expose, implicit_reducible]
public def instruction (op : ClassicalOp input output ctx ctx) : Circuit execution ctx ctx :=
  .classical (selectedApplication (execution := execution) op)

/-- The actual native path is precisely the declared output value. -/
public def instructionPathEquiv (op : ClassicalOp input output ctx ctx) :
    (instruction (execution := execution) op).Path ≃ output.Value :=
  Equiv.cast (congrArg CShape.Value (selectedApplication_output (execution := execution) op))

/-- Complete deterministic caller update and actual returned native path. -/
public def instructionStep (op : ClassicalOp input output ctx ctx) (store : Store ctx) :
    Store ctx × (instruction (execution := execution) op).Path :=
  (store.applyOp op, (instructionPathEquiv (execution := execution) op).symm
    (op.eval (store.read op.inputRef)))

/-- The selected leaf executes its fixed value semantics without changing the shared service. -/
public lemma bitWord_instruction_execute (op : ClassicalOp input output ctx ctx)
    (environment : execution.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (execution.HiddenState × History)) :
    (instruction (execution := execution) op).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := instructionStep (execution := execution) op entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = model at same
      cases same
      exact (Circuit.execute_classical_mapClassical (model := .classical model services) environment
        (application op) op.eval
        (bitWord_application_evaluate op) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = model at same
      cases same
      exact (Circuit.execute_classical_mapClassical
        (model := .quantum gates oracles model services) environment (application op) op.eval
        (bitWord_application_evaluate op) Reference state).trans
          (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- Every selected leaf emits its one width-indexed native event. -/
public lemma bitWord_instruction_eventTrace (op : ClassicalOp input output ctx ctx)
    (path : (instruction (execution := execution) op).Path) :
    (instruction (execution := execution) op).eventTrace path =
      [.classicalOperation (selectedCoordinate (execution := execution) op.label)] := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = model at same
      cases same
      exact congrArg (fun coordinate =>
        [Resource.Event.classicalOperation (model := .classical model services) coordinate])
        (bitWord_application_coordinate op)
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = model at same
      cases same
      exact congrArg (fun coordinate =>
        [Resource.Event.classicalOperation
          (model := .quantum gates oracles model services) coordinate])
        (bitWord_application_coordinate op)

/-- The actual native duration is charged once in the dependency expression. -/
public lemma bitWord_instruction_depth (op : ClassicalOp input output ctx ctx)
    (duration : Resource.Event execution → Nat)
    (path : (instruction (execution := execution) op).Path) :
    (instruction (execution := execution) op).depth duration path =
      duration (.classicalOperation (selectedCoordinate (execution := execution) op.label)) := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = model at same
      cases same
      exact congrArg (fun coordinate => duration (.classicalOperation coordinate))
        (bitWord_application_coordinate op)
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = model at same
      cases same
      exact congrArg (fun coordinate => duration (.classicalOperation coordinate))
        (bitWord_application_coordinate op)

end

end QuantumAlg.BitWord
