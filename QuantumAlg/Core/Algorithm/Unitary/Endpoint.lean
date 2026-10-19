/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete unitary execution against an independent specification

The target operator, resource limits and timing are specification inputs. A
separate actual circuit must implement that operator and satisfy those limits.
The complete output retains every live system and classical cell. The state
contract includes arbitrary correlations with an external reference.
-/

namespace QuantumAlg.UnitaryExecution
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

/-- **Input.** Any normalized state on the supplied context and external reference.
**Output.** The same live context after the specified mathematical unitary acts.
**Resource budget.** Independently supplied event, resident, auxiliary and quantum time limits.
**Success.** Exact full joint-state action with probability one and borrowed restoration.
**Source.** The complete-state unitary semantics of the typed execution model. -/
public def problem (operator : oracles.Interpretation → UnitaryOperator ctx.register)
    (resources : ResourceBudget (.quantum gates oracles))
    (quantumTimeLimit : Nat) :
    Problem (.quantum gates oracles) ctx ctx .unit where
  Witness := Unit
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ _ => True
  successLB := fun _ _ => ⟨1, le_rfl⟩
  states := fun environment _ => [StateRequirement.unitary (operator environment.quantum)]
  resources := resources
  quantumTimeLimit := quantumTimeLimit

/-- Execute the actual native construction and retain the entire live context. -/
public def algorithm (program : UnitaryCircuit gates oracles ctx.quantumLayout) :
    Algorithm (.quantum gates oracles) ctx ctx .unit where
  run := { code := .unitary program, output := Output.all ctx .unit }

/-- An owned-interface implementation satisfies the complete independent unitary contract. -/
theorem main (operator : oracles.Interpretation → UnitaryOperator ctx.register)
    (resources : ResourceBudget (.quantum gates oracles))
    (quantumTimeLimit : Nat)
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (same : ∀ environment, program.matrix environment = operator environment)
    (noClassical : ctx.borrowedClassicalShape = .unit)
    (noQuantum : ctx.borrowedQuantumWires = [])
    (events : program.eventCost ≤ resources.events)
    (resident : ctx.residentSpace ≤ resources.resident)
    (auxiliary : ctx.auxiliarySpace ≤ resources.auxiliary)
    (timing : program.evaluatedEventDepth Resource.Event.quantumDuration ≤ quantumTimeLimit) :
    Algorithm.Solves (algorithm program) (problem operator resources quantumTimeLimit) := by
  constructor
  · intro environment _witness Reference input _valid _initialization
    apply le_of_eq
    symm
    apply (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
    intro _pair _supported
    trivial
  · intro environment _witness Reference input _valid _initialization requirement present
    have sameRequirement : requirement = StateRequirement.unitary (operator environment.quantum) :=
      List.mem_singleton.mp present
    subst requirement
    exact StateRequirement.unitary_holds environment (operator environment.quantum)
      program (same environment.quantum) (Output.all ctx .unit) input
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
end QuantumAlg.UnitaryExecution
