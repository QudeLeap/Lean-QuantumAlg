/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Borrowed.State
public import QuantumAlg.Core.Execution.Probability
public import QuantumAlg.Core.Execution.Input
public import QuantumAlg.Core.Execution.Output
public import QuantumAlg.Core.Execution.Trace
public import QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Interpret
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Input
import all QuantumAlg.Core.Execution.Probability

/-!
# Complete executions of one circuit

A run consists of a circuit and an explicit complete Output. The unique
circuit interpreter produces its quantum state, final classical store, and
actual path. The initial classical value is retained as a mathematical record
so relational success events remain meaningful for correlated inputs.

Probabilities are the traces of those actual state blocks. No transition,
distribution, event account, space peak, or depth witness is supplied by the
caller. Historical records and the external reference add no physical storage.
-/

namespace QuantumAlg

/-- One circuit with an explicit manifest of every live final resource. -/
public structure AlgorithmRun {kind : ProblemKind} (pre post : RuntimeCtx kind)
    (outputShape : CShape) : Type 1 where
  /-- The sole executable program. -/
  code : Circuit pre post
  /-- Every final live entry is explicitly accounted for. -/
  output : Output post outputShape

namespace AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {pre post : RuntimeCtx kind} {outputShape : CShape}

/-- Actual final storage, initial classical input, and the interpreter's path. -/
public abbrev Record (run : AlgorithmRun pre post outputShape) :=
  Execution.Store post × (Execution.Store pre × run.code.Path)

/-- Execute once, retaining the initial store only as a mathematical history. -/
public def execute (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    ExecutionState run.Record (Register.prod post.register Reference) :=
  run.code.execute Reference (input.mapClassical (fun store => (store, store)))

/-- Complete execution preserves the incoming mass. -/
theorem execute_mass (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    (run.execute Reference input).mass = input.mass := by
  exact (run.code.execute_mass Reference _).trans (input.mapClassical_mass _)

/-- Complete execution of a certified input has total probability one. -/
theorem execute_normalized (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run.execute Reference input.state).IsNormalized :=
  (run.execute_mass Reference input.state).trans input.normalized

/-- Forget mathematical histories while retaining every actual final cell and wire. -/
public def finalState (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    ExecutionState (Execution.Store post) (Register.prod post.register Reference) :=
  (run.execute Reference input).mapClassical Prod.fst

/-- Forgetting the execution records does not change probability mass. -/
theorem finalState_mass (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    (run.finalState Reference input).mass = input.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (run.execute_mass Reference input)

/-- The shaped result is read from the actual final store. -/
public def result (run : AlgorithmRun pre post outputShape) (record : run.Record) :
    outputShape.Value := run.output.eval record.1

/-- Actual finite execution distribution, derived from normalized state block traces. -/
public def executionDistribution (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) : PMF run.Record :=
  (run.execute Reference input.state).toPMF (run.execute_normalized input)

/-- Output probabilities are a projection of that same execution distribution. -/
public def outputDistribution (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) : PMF outputShape.Value :=
  (run.executionDistribution input).map run.result

/-- The initial classical value and actual result remain jointly observable. -/
public def relationalDistribution (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) :
    PMF (Execution.Store pre × outputShape.Value) :=
  (run.executionDistribution input).map (fun record => (record.2.1, run.result record))

/-- Ordered native event traces of the actual executions. -/
public def eventTraceDistribution (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) :
    PMF (List (Resource.Event kind)) :=
  (run.executionDistribution input).map (fun record => run.code.eventTrace record.2.2)

/-- State blocks indexed only by the actual circuit path, summing both stores. -/
public def pathState (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    ExecutionState run.code.Path (Register.prod post.register Reference) :=
  (run.execute Reference input).mapClassical (fun record => record.2.2)

/-- Probability of an actual path, including all classical values that realize it. -/
public def pathMass (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference))
    (path : run.code.Path) : ℝ :=
  ((run.pathState Reference input).block path).mass

/-- The actual execution restores all borrowed classical, quantum and reference correlations. -/
public def RestoresBorrowed (run : AlgorithmRun pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) : Prop :=
  run.code.BorrowedRestored Reference
    (input.state.mapClassical (fun store => (store, store)))
    (run.execute Reference input.state)

/-- Only positive-probability paths impose execution-dependent resource obligations. -/
public def Supports (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference))
    (path : run.code.Path) : Prop := 0 < run.pathMass Reference input path

/-- Path probabilities sum to the actual input mass. -/
theorem sum_pathMass (run : AlgorithmRun pre post outputShape) (Reference : Register)
    (input : ExecutionState (Execution.Store pre) (Register.prod pre.register Reference)) :
    ∑ path, run.pathMass Reference input path = input.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (run.execute_mass Reference input)

end

end AlgorithmRun

end QuantumAlg
