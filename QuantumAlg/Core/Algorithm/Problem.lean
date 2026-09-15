/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.State.Requirement
public import QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.State.Requirement

/-!
# Independent problems for complete circuit executions

A problem owns its input domain, accepted classical outputs, success threshold,
state requirements, and explicit native resource limits. Its type contains no
implementation from which to obtain those limits. Input validity sees only the
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
public structure ResourceBudget (kind : ProblemKind) where
  /-- A separate bound at each declaration-owned native event coordinate. -/
  events : ResourcePool kind
  /-- Peak number of live classical bits and systems at each actual dimension. -/
  resident : SpacePool kind
  /-- Peak live storage whose declared role is auxiliary. -/
  auxiliary : SpacePool kind

/-- Only quantum specifications contain event durations and a depth limit. -/
public inductive DepthBudget : ProblemKind → Type where
  /-- Classical specifications carry no quantum depth data. -/
  | classical : DepthBudget .classical
  /-- Native event durations and an independently stated critical-path bound. -/
  | quantum (duration : Resource.Event .quantum → Nat) (limit : Nat) : DepthBudget .quantum

namespace DepthBudget

/-- Evaluate the circuit's actual path under the specification's event durations. -/
public def Holds {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (budget : DepthBudget kind) (code : Circuit pre post) (path : code.Path) : Prop :=
  match kind, budget, pre, post, code, path with
  | .classical, .classical, _, _, _, _ => True
  | .quantum, .quantum duration limit, _, _, code, path => code.depth duration path ≤ limit

end DepthBudget

/-- An implementation-independent contract on exact input and output contexts. -/
public structure Problem (kind : ProblemKind) (pre post : RuntimeCtx kind)
    (outputShape : CShape) : Type 1 where
  /-- Input admissibility depends only on the reference marginal, retaining classical blocks. -/
  valid : ExecutionState (Execution.Store pre) pre.register → Prop
  /-- Acceptance relates the actual initial classical value to the actual final result. -/
  accepts : Execution.Store pre → outputShape.Value → Prop
  /-- Required probability of that relational event. -/
  successLB : ProbabilityLowerBound
  /-- Pure, mixed, marginal, joint or dirty state obligations on actual final observations. -/
  states : List (StateRequirement pre post)
  /-- Explicit native event and space limits supplied by the specification. -/
  resources : ResourceBudget kind
  /-- Quantum event-duration interpretation and limit, absent for classical problems. -/
  depth : DepthBudget kind

/-- One complete run, without independently cached execution or accounting data. -/
public structure Algorithm (kind : ProblemKind) (pre post : RuntimeCtx kind)
    (outputShape : CShape) : Type 1 where
  /-- The sole source of quantum/classical semantics, outputs, paths and resource use. -/
  run : AlgorithmRun pre post outputShape

namespace Algorithm

noncomputable section

variable {kind : ProblemKind} {pre post : RuntimeCtx kind} {outputShape : CShape}

/-- The algorithm's actual normalized execution distribution. -/
public def executionDistribution (algorithm : Algorithm kind pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) : PMF algorithm.run.Record :=
  algorithm.run.executionDistribution input

/-- The actual final output distribution, projected from the same complete execution. -/
public def outputDistribution (algorithm : Algorithm kind pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) : PMF outputShape.Value :=
  algorithm.run.outputDistribution input

/-- Initial classical input and actual output are observed jointly for success events. -/
public def relationalDistribution (algorithm : Algorithm kind pre post outputShape)
    {Reference : Register} (input : Execution.Input pre Reference) :
    PMF (Execution.Store pre × outputShape.Value) :=
  algorithm.run.relationalDistribution input

end

end Algorithm

end QuantumAlg
