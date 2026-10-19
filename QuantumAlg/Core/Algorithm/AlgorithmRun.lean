/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Probability
public import QuantumAlg.Core.Execution.Input.Oracle
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Probability

/-!
# Complete executions of one circuit

A run consists of a circuit and an explicit complete Output. The interpreter
uses the explicit environment to produce its quantum state, final classical store, and
actual path. Its persistent service state is supplied once with the input.
The initial classical value is retained as a mathematical record
so relational success events remain meaningful for correlated inputs.

Probabilities are the traces of those actual state blocks. The interpreter
derives every distribution, event account, space peak and depth observation.
Historical records, service state and the external reference add no
caller-addressable physical storage.
-/

namespace QuantumAlg

/-- One circuit with an explicit manifest of every live final resource. -/
public structure AlgorithmRun (model : ExecutionModel) (pre post : RuntimeCtx model.kind)
    (outputShape : CShape) (allowAllocation : Bool := true) : Type 1 where
  /-- The sole executable program. -/
  code : Circuit model pre post allowAllocation
  /-- Every final live entry is explicitly accounted for. -/
  output : Output post outputShape

namespace AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {allowAllocation : Bool} {model : ExecutionModel}
  {pre post : RuntimeCtx model.kind} {outputShape : CShape}

/-- Actual final store and service state, initial caller store and interpreter path. -/
public abbrev Record (run : AlgorithmRun model pre post outputShape allowAllocation) :=
  Execution.Store post × (model.HiddenState × (Execution.Store pre × run.code.Path))

/-- Execute once, retaining the initial store only as a mathematical history. -/
public def execute (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    ExecutionState run.Record (Register.prod post.register Reference) :=
  run.code.execute environment Reference
    (input.mapClassical (fun value => (value.1, (value.2, value.1))))

/-- Complete execution preserves the incoming mass. -/
lemma execute_mass (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    (run.execute environment Reference input).mass = input.mass := by
  exact (run.code.execute_mass environment Reference _).trans (input.mapClassical_mass _)

/-- Complete execution of a certified input has total probability one. -/
lemma execute_normalized (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    (run.execute environment Reference input.state).IsNormalized :=
  (run.execute_mass environment Reference input.state).trans input.normalized

/-- Forget mathematical histories while retaining every actual final cell and wire. -/
public def finalState (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    ExecutionState (Execution.Store post) (Register.prod post.register Reference) :=
  (run.execute environment Reference input).mapClassical Prod.fst

/-- Recording the initial store and forgetting the final history leave the
complete quantum-reference marginal equal to the circuit execution. -/
lemma finalState_quantumMarginal (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    (run.finalState environment Reference input).quantumMarginal =
      (run.code.execute environment Reference
        (input.mapClassical (fun value => (value.1, (value.2, value.1))))).quantumMarginal := by
  rw [finalState, ExecutionState.mapClassical_quantumMarginal, execute]

/-- Forgetting the execution records does not change probability mass. -/
lemma finalState_mass (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    (run.finalState environment Reference input).mass = input.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (run.execute_mass environment Reference input)

/-- The shaped result is read from the actual final store. -/
@[expose] public def result (run : AlgorithmRun model pre post outputShape allowAllocation)
    (record : run.Record) :
    outputShape.Value := run.output.eval record.1

/-- Actual finite execution distribution, derived from normalized state block traces. -/
public def executionDistribution (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : PMF run.Record :=
  (run.execute environment Reference input.state).toPMF (run.execute_normalized environment input)

/-- Output probabilities are a projection of that same execution distribution. -/
public def outputDistribution (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : PMF outputShape.Value :=
  (run.executionDistribution environment input).map run.result

/-- The initial classical value and actual result remain jointly observable. -/
public def relationalDistribution (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    PMF (Execution.Store pre × outputShape.Value) :=
  (run.executionDistribution environment input).map
    (fun record => (record.2.2.1, run.result record))

/-- Ordered native event traces of the actual executions. -/
public def eventTraceDistribution (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    PMF (List (Resource.Event model)) :=
  (run.executionDistribution environment input).map (fun record => run.code.eventTrace record.2.2.2)

/-- State blocks indexed only by the actual circuit path, summing both stores. -/
public def pathState (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    ExecutionState run.code.Path (Register.prod post.register Reference) :=
  (run.execute environment Reference input).mapClassical (fun record => record.2.2.2)

/-- Probability of an actual path, including all classical values that realize it. -/
public def pathMass (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference))
    (path : run.code.Path) : ℝ :=
  ((run.pathState environment Reference input).block path).mass

/-- The actual execution restores all borrowed classical, quantum and reference correlations. -/
public def RestoresBorrowed (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : Prop :=
  run.code.BorrowedRestored Reference input.state (run.execute environment Reference input.state)

/-- Only positive-probability paths impose execution-dependent resource obligations. -/
public def Supports (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference))
    (path : run.code.Path) : Prop := 0 < run.pathMass environment Reference input path

/-- Path probabilities sum to the actual input mass. -/
lemma sum_pathMass (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment)
    (Reference : Register)
    (input : ExecutionState (Execution.Store pre × model.HiddenState)
      (Register.prod pre.register Reference)) :
    ∑ path, run.pathMass environment Reference input path = input.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (run.execute_mass environment Reference input)

end

end AlgorithmRun

end QuantumAlg
