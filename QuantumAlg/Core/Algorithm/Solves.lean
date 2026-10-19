/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Borrowed.State

/-!
# Correctness and native bounds for the same actual execution

Every obligation ranges over every oracle environment and specification witness,
normalized inputs and all external reference
extensions admitted by the local caller and joint service initialization
contracts. Success uses the joint initial
classical value and actual output. State promises observe actual final values
and sum unobserved histories. Borrowed restoration is a separate mandatory
comparison of the complete borrowed classical-quantum-reference state.

Event counts, resident and auxiliary peaks, and quantum computation time are constrained only on
positive-probability paths of that very execution. The limits belong to the
independent problem, never to a caller-supplied account of the run.
-/

namespace QuantumAlg.Algorithm

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Complete correctness, restoration and native resource bounds for one typed algorithm. -/
public structure Solves {allowAllocation : Bool} {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {outputShape : CShape}
    (algorithm : Algorithm model pre post outputShape allowAllocation)
    (problem : Problem model pre post outputShape) : Prop where
  /-- Success retains the correlation between each initial classical value and its result. -/
  success : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      (problem.successLB environment witness).value ≤
      (algorithm.relationalDistribution environment input).toOuterMeasure
        {pair | problem.accepts environment witness pair.1 pair.2}
  /-- Every independent output state requirement holds after the actual final observation. -/
  states : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      ∀ requirement ∈ problem.states environment witness,
      requirement.Holds input.caller (algorithm.run.finalState environment Reference input.state)
  /-- All borrowed resources and their joint correlations are restored, regardless of promises. -/
  borrowed : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      algorithm.run.RestoresBorrowed environment input
  /-- Native event counts of every actual supported execution satisfy the independent limits. -/
  events : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      ∀ path,
      algorithm.run.Supports environment Reference input.state path →
        algorithm.run.code.resourcePool path ≤ problem.resources.events
  /-- Every supported path respects its actual resident-space peak. -/
  resident : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      ∀ path,
      algorithm.run.Supports environment Reference input.state path →
        algorithm.run.code.peakResidentSpace path ≤ problem.resources.resident
  /-- Every supported path respects its actual auxiliary-space peak. -/
  auxiliary : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      ∀ path,
      algorithm.run.Supports environment Reference input.state path →
        algorithm.run.code.peakAuxiliarySpace path ≤ problem.resources.auxiliary
  /-- Quantum computation time evaluates the dependencies of that same supported path. -/
  time : ∀ (environment : model.Environment) (witness : problem.Witness) (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference),
    problem.valid environment witness input.caller.localState →
    problem.initialization environment witness input.localState →
      ∀ path,
      algorithm.run.Supports environment Reference input.state path →
        algorithm.quantumTime path ≤ problem.quantumTimeLimit

end

end QuantumAlg.Algorithm
