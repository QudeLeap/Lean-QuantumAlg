/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Requirement
public import QuantumAlg.Core.Algorithm.AlgorithmRun
public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent problems for complete circuit executions

A problem owns its specification-only witness type, input domain, accepted
classical outputs, success threshold,
state requirements, oracle initialization and explicit native resource limits.
Its type contains no implementation from which to obtain those limits. Input validity sees only the
local classical and quantum state; it cannot exclude an external reference
extension of that same input.

An algorithm contains only its complete run. Solving a problem additionally
requires restoration of every borrowed resource and its joint correlations;
output state promises cannot waive that separate obligation.
-/

namespace QuantumAlg

/-- A probability threshold certified to be at most one. -/
public structure ProbabilityLowerBound where
  /-- Required probability of the independently stated accepted event. -/
  value : ENNReal
  /-- A success requirement cannot exceed total probability. -/
  le_one : value ≤ 1

/-- Independently supplied native event and live-storage limits. -/
public structure ResourceBudget (model : ExecutionModel) where
  /-- A separate bound at each declaration-owned native event coordinate. -/
  events : ResourcePool model
  /-- Peak number of live classical bits and systems at each actual dimension. -/
  resident : SpacePool model.kind
  /-- Peak live storage whose declared role is auxiliary. -/
  auxiliary : SpacePool model.kind

/-- An implementation-independent contract on exact input and output contexts. -/
public structure Problem (model : ExecutionModel) (pre post : RuntimeCtx model.kind)
    (outputShape : CShape) : Type 1 where
  /-- Source-level hidden data used only to state the specification. -/
  Witness : Type
  /-- Input admissibility depends only on the reference marginal, retaining classical blocks. -/
  valid : model.Environment → Witness → ExecutionState (Execution.Store pre) pre.register → Prop
  /-- Admissible local joint caller/service initialization, independent of the implementation.
  Every external reference extension of an admitted joint input is still quantified. -/
  initialization : model.Environment → Witness →
    ExecutionState (Execution.Store pre × model.HiddenState) pre.register → Prop
  /-- Acceptance relates the actual initial classical value to the actual final result. -/
  accepts : model.Environment → Witness → Execution.Store pre → outputShape.Value → Prop
  /-- Required probability of that relational event. -/
  successLB : model.Environment → Witness → ProbabilityLowerBound
  /-- Pure, mixed, marginal, joint or dirty state obligations on actual final observations. -/
  states : model.Environment → Witness → List (StateRequirement pre post)
  /-- Explicit native event and space limits supplied by the specification. -/
  resources : ResourceBudget model
  /-- Independent bound on the complete actual execution's quantum computation time. -/
  quantumTimeLimit : Nat

namespace Problem

/-- Both the local caller domain and the joint service initialization must hold. -/
public def Admits {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {shape : CShape} (problem : Problem model pre post shape)
    (environment : model.Environment) (witness : problem.Witness) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : Prop :=
  problem.valid environment witness input.caller.localState ∧
    problem.initialization environment witness input.localState

end Problem

/-- One complete run, without independently cached execution or accounting data. -/
public structure Algorithm (model : ExecutionModel) (pre post : RuntimeCtx model.kind)
    (outputShape : CShape) (allowAllocation : Bool := true) : Type 1 where
  /-- The sole source of quantum/classical semantics, outputs, paths and resource use. -/
  run : AlgorithmRun model pre post outputShape allowAllocation

namespace Algorithm

noncomputable section

variable {allowAllocation : Bool} {model : ExecutionModel}
  {pre post : RuntimeCtx model.kind} {outputShape : CShape}

/-- Quantum computation time is evaluated on the sole actual run and its recorded path. -/
@[expose] public def quantumTime (algorithm : Algorithm model pre post outputShape allowAllocation)
    (path : algorithm.run.code.Path) : Nat :=
  algorithm.run.code.quantumTime path

/-- The algorithm's actual normalized execution distribution. -/
public def executionDistribution (algorithm : Algorithm model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    PMF algorithm.run.Record :=
  algorithm.run.executionDistribution environment input

/-- The actual final output distribution, projected from the same complete execution. -/
public def outputDistribution (algorithm : Algorithm model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) : PMF outputShape.Value :=
  algorithm.run.outputDistribution environment input

/-- Initial classical input and actual output are observed jointly for success events. -/
public def relationalDistribution (algorithm : Algorithm model pre post outputShape allowAllocation)
    (environment : model.Environment)
    {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference) :
    PMF (Execution.Store pre × outputShape.Value) :=
  algorithm.run.relationalDistribution environment input

end

end Algorithm

end QuantumAlg
