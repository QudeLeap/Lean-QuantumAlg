/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Endpoint
public import QuantumAlg.Core.Algorithm.Unitary.Approximation
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Algorithm.Unitary.Approximation
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete approximate unitary execution

All live systems and the external reference satisfy the independent unitary
neighborhood target. The exact same run supplies the success, restoration,
event, space and time obligations.
-/

namespace QuantumAlg.UnitaryExecution.Approximate
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

/-- **Input.** Any normalized joint state on the supplied context and external reference.
**Output.** Every live system, transformed by a unitary within the given operator-norm error.
**Resource budget.** Independent event, resident, auxiliary and quantum time limits.
**Success.** Probability one, the full reference-aware neighborhood target and borrowed restoration.
**Source.** Complete-state unitary semantics and full-phase operator-norm approximation. -/
public def problem (operator : oracles.Interpretation → UnitaryOperator ctx.register)
    (error : ℝ) (nonnegative : 0 ≤ error)
    (resources : ResourceBudget (.quantum gates oracles)) (quantumTimeLimit : Nat) :
    Problem (.quantum gates oracles) ctx ctx .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun environment _ =>
    [StateRequirement.approximateUnitary (operator environment.quantum) error nonnegative]
  resources := resources
  quantumTimeLimit := quantumTimeLimit

/-- The actual unitary program satisfies every obligation of its independent approximate target. -/
theorem main (operator : oracles.Interpretation → UnitaryOperator ctx.register)
    (error : ℝ) (nonnegative : 0 ≤ error)
    (resources : ResourceBudget (.quantum gates oracles)) (quantumTimeLimit : Nat)
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (close : ∀ environment, HilbertOperator.opNorm
      ((program.matrix environment : HilbertOperator ctx.register) -
        (operator environment : HilbertOperator ctx.register)) ≤ error)
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = [])
    (events : program.eventCost ≤ resources.events)
    (resident : ctx.residentSpace ≤ resources.resident)
    (auxiliary : ctx.auxiliarySpace ≤ resources.auxiliary)
    (timing : program.evaluatedEventDepth Resource.Event.quantumDuration ≤ quantumTimeLimit) :
    Algorithm.Solves (UnitaryExecution.algorithm program)
      (problem operator error nonnegative resources quantumTimeLimit) := by
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialization requirement present
    have sameRequirement : requirement =
        StateRequirement.approximateUnitary (operator environment.quantum) error nonnegative :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.approximateUnitary_holds environment (operator environment.quantum)
      error nonnegative program (close environment.quantum) (Output.all ctx .unit) input
  · intro environment _witness Reference input _valid _initialization
    exact AlgorithmRun.restoresBorrowed_unitary_noBorrowed environment noClassical noQuantum
      program (Output.all ctx .unit) input
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    change ResourcePool.ofList program.eventTrace ≤ resources.events
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost]
    exact events
  · intro _environment _witness _Reference _input _valid _initialization path _supported axis
    change Nat.max (ctx.residentSpace axis) 0 ≤ resources.resident axis
    exact (le_of_eq (Nat.max_zero _)).trans (resident axis)
  · intro _environment _witness _Reference _input _valid _initialization path _supported axis
    change Nat.max (ctx.auxiliarySpace axis) 0 ≤ resources.auxiliary axis
    exact (le_of_eq (Nat.max_zero _)).trans (auxiliary axis)
  · intro _environment _witness _Reference _input _valid _initialization path _supported
    exact timing

end
end QuantumAlg.UnitaryExecution.Approximate
