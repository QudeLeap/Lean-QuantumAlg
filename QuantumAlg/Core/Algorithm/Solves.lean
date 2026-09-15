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

Every obligation ranges over normalized inputs and all external reference
extensions admitted by the local input domain. Success uses the joint initial
classical value and actual output. State promises observe actual final values
and sum unobserved histories. Borrowed restoration is a separate mandatory
comparison of the complete borrowed classical-quantum-reference state.

Event counts, resident and auxiliary peaks, and depth are constrained only on
positive-probability paths of that very execution. The limits belong to the
independent problem, never to a caller-supplied account of the run.
-/

namespace QuantumAlg.Algorithm

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Complete correctness, restoration and native resource bounds for one typed algorithm. -/
public structure Solves {kind : ProblemKind} {pre post : RuntimeCtx kind} {outputShape : CShape}
    (algorithm : Algorithm kind pre post outputShape)
    (problem : Problem kind pre post outputShape) : Prop where
  /-- Success retains the correlation between each initial classical value and its result. -/
  success : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → problem.successLB.value ≤
      (algorithm.relationalDistribution input).toOuterMeasure
        {pair | problem.accepts pair.1 pair.2}
  /-- Every independent output state requirement holds after the actual final observation. -/
  states : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → ∀ requirement ∈ problem.states,
      requirement.Holds input (algorithm.run.finalState Reference input.state)
  /-- All borrowed resources and their joint correlations are restored, regardless of promises. -/
  borrowed : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → algorithm.run.RestoresBorrowed input
  /-- Native event counts of every actual supported execution satisfy the independent limits. -/
  events : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → ∀ path,
      algorithm.run.Supports Reference input.state path →
        algorithm.run.code.resourcePool path ≤ problem.resources.events
  /-- Every supported path respects its actual resident-space peak. -/
  resident : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → ∀ path,
      algorithm.run.Supports Reference input.state path →
        algorithm.run.code.peakResidentSpace path ≤ problem.resources.resident
  /-- Every supported path respects its actual auxiliary-space peak. -/
  auxiliary : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → ∀ path,
      algorithm.run.Supports Reference input.state path →
        algorithm.run.code.peakAuxiliarySpace path ≤ problem.resources.auxiliary
  /-- Quantum depth evaluates the dependencies of that same supported path. -/
  depth : ∀ (Reference : Register) (input : Execution.Input pre Reference),
    problem.valid input.localState → ∀ path,
      algorithm.run.Supports Reference input.state path →
        problem.depth.Holds algorithm.run.code path

end

end QuantumAlg.Algorithm
