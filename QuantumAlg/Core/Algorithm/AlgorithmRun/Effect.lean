/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual algorithm output probabilities as certified effect observations

The complete run executes its stored circuit and reads the declared Output
from the actual final Store. Output events and relations with the retained
initial Store are exact indicator-effect observations of those same records.
The complete quantum register and arbitrary external reference are retained.
The same circuit's certified pullback returns each observable to the original
joint caller and persistent-service input, including the exact duplicated
initial caller Store. Service initialization is supplied once by that input.
-/

namespace QuantumAlg.AlgorithmRun

variable {allowAllocation : Bool}

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {outputShape : CShape}

/-- Reading any finite event from actual execution records equals its indicator-effect weight. -/
lemma executionDistribution_map_eq_effectWeight (run : AlgorithmRun model pre post outputShape
  allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    {Value : Type} [Finite Value] [valueDecision : DecidableEq Value]
    (read : run.Record → Value) (value : Value) :
    (run.executionDistribution environment input).map read value =
      ENNReal.ofReal ((run.execute environment Reference input.state).effectWeight (fun record =>
        if read record = value then Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference))) := by
  cases Subsingleton.elim valueDecision (Classical.decEq Value)
  let := Fintype.ofFinite Value
  have mapped := congrArg (fun distribution : PMF Value => distribution value)
    (ExecutionState.toPMF_mapClassical (run.execute environment Reference input.state)
      (run.execute_normalized environment input) read)
  exact mapped.symm.trans (congrArg ENNReal.ofReal
    (ExecutionState.effectWeight_observed_mass
      (run.execute environment Reference input.state) read value).symm)

/-- A shaped output value is observed through the run's actual complete Output evaluation. -/
lemma outputDistribution_apply_eq_effectWeight (run : AlgorithmRun model pre post outputShape
  allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    (value : outputShape.Value) :
    run.outputDistribution environment input value =
      ENNReal.ofReal ((run.execute environment Reference input.state).effectWeight (fun record =>
        if run.result record = value then Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference))) :=
  executionDistribution_map_eq_effectWeight run environment input run.result value

/-- The original Store and actual shaped result have their exact joint event probability. -/
lemma relationalDistribution_apply_eq_effectWeight
  (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    (value : Execution.Store pre × outputShape.Value) :
    run.relationalDistribution environment input value =
      ENNReal.ofReal ((run.execute environment Reference input.state).effectWeight (fun record =>
        if (record.2.2.1, run.result record) = value then
          Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference))) :=
  executionDistribution_map_eq_effectWeight run environment input
    (fun record => (record.2.2.1, run.result record)) value

/-- Any Boolean output event is evaluated on the actual declared output, with exact probability. -/
lemma outputDistribution_event_eq_effectWeight (run : AlgorithmRun model pre post outputShape
  allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    (event : outputShape.Value → Bool) :
    (run.outputDistribution environment input).map event true =
      ENNReal.ofReal ((run.execute environment Reference input.state).effectWeight (fun record =>
        if event (run.result record) = true then Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference))) := by
  rw [outputDistribution, PMF.map_comp]
  exact executionDistribution_map_eq_effectWeight run environment input (event ∘ run.result) true

/-- Boolean relational success uses the retained original Store and the actual final result. -/
lemma relationalDistribution_event_eq_effectWeight
  (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    (event : Execution.Store pre × outputShape.Value → Bool) :
    (run.relationalDistribution environment input).map event true =
      ENNReal.ofReal ((run.execute environment Reference input.state).effectWeight (fun record =>
        if event (record.2.2.1, run.result record) = true then
          Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference))) := by
  rw [relationalDistribution, PMF.map_comp]
  exact executionDistribution_map_eq_effectWeight run environment input
    (fun record => event (record.2.2.1, run.result record)) true

/-- The same circuit pulls final observables to the actual input and its initial Store record. -/
def effectPullback (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
  (Reference : Register)
    (effects : run.Record → Effect (Register.prod post.register Reference)) :
    Execution.Store pre × model.HiddenState → Effect (Register.prod pre.register Reference) :=
  fun original => run.code.effectPullback environment Reference effects
    (original.1, (original.2, original.1))

/-- Exact algorithm execution pulls observations through the circuit and its real history map. -/
lemma effectWeight_execute (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
  (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference))
    (effects : run.Record → Effect (Register.prod post.register Reference)) :
    (run.execute environment Reference input).effectWeight effects =
      input.effectWeight (run.effectPullback environment Reference effects) := by
  unfold execute
  rw [Circuit.effectWeight_execute, ExecutionState.effectWeight_mapClassical_decision]
  rfl

/-- Every finite execution-record event has its exact effect weight on the original input. -/
lemma executionDistribution_map_eq_input_effectWeight
    (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    {Value : Type} [Finite Value] [DecidableEq Value]
    (read : run.Record → Value) (value : Value) :
    (run.executionDistribution environment input).map read value =
      ENNReal.ofReal (input.state.effectWeight
        (run.effectPullback environment Reference (fun record =>
        if read record = value then Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference)))) := by
  rw [executionDistribution_map_eq_effectWeight, effectWeight_execute]

/-- Actual Boolean output success is the certified pulled effect on the complete original input. -/
lemma outputDistribution_event_eq_input_effectWeight
    (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register} (input : Execution.OracleInput model.classicalOracles pre Reference)
    (event : outputShape.Value → Bool) :
    (run.outputDistribution environment input).map event true =
      ENNReal.ofReal (input.state.effectWeight
        (run.effectPullback environment Reference (fun record =>
        if event (run.result record) = true then Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference)))) := by
  rw [outputDistribution_event_eq_effectWeight, effectWeight_execute]

/-- Relational success pulls back the real Output and the historical initial Store. -/
lemma relationalDistribution_event_eq_input_effectWeight
    (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (event : Execution.Store pre × outputShape.Value → Bool) :
    (run.relationalDistribution environment input).map event true =
      ENNReal.ofReal (input.state.effectWeight
        (run.effectPullback environment Reference (fun record =>
        if event (record.2.2.1, run.result record) = true then
          Effect.one (Register.prod post.register Reference)
        else Effect.zero (Register.prod post.register Reference)))) := by
  rw [relationalDistribution_event_eq_effectWeight, effectWeight_execute]

end

end QuantumAlg.AlgorithmRun
