/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Classical.Predicate

/-!
# Native gates do not satisfy a physical restart contract

A gate-only execution has no recorded measurement and is not classical.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- A single native gate has no measured result for a quantum restart. -/
lemma singleGate_noRestart
    (environment :
      (.quantum gates oracles operations classicalOracles : ExecutionModel).Environment)
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ Nonempty (RestartCleanup
      (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
        (classicalOracles := classicalOracles) body) environment) := by
  intro ⟨boundary⟩
  obtain ⟨dimension, present⟩ := boundary.measured ()
  change (Resource.Event.measurement dimension :
    Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
      body.eventTrace operations classicalOracles at present
  rw [trace] at present
  simp at present

/-- The second native gate cannot be hidden in a classical tail. -/
lemma singleGate_notClassical
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ IsClassical (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
      (classicalOracles := classicalOracles) body) := by
  intro classical
  have present : (Resource.Event.gate coordinate :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
        (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
          (classicalOracles := classicalOracles) body).eventTrace () := by
    change (Resource.Event.gate coordinate :
      Resource.Event (.quantum gates oracles operations classicalOracles)) ∈
        body.eventTrace operations classicalOracles
    rw [trace]
    simp
  rcases classical () (.gate coordinate) present with
    ⟨_, impossible⟩ | ⟨_, impossible⟩
  · cases impossible
  · cases impossible

/-- A native gate cannot be classified as classical or as a measured restart. -/
lemma twoSingleGates_noSplit
    (environment :
      (.quantum gates oracles operations classicalOracles : ExecutionModel).Environment)
    (body : UnitaryCircuit gates oracles ctx.quantumLayout)
    (coordinate : gates.Coordinate)
    (trace : body.eventTrace operations classicalOracles = [.gate coordinate]) :
    ¬ (IsClassical (Circuit.unitary (allowAllocation := allowAllocation) (operations := operations)
          (classicalOracles := classicalOracles) body) ∨
        Nonempty (RestartCleanup (Circuit.unitary
            (allowAllocation := allowAllocation)
            (operations := operations)
          (classicalOracles := classicalOracles) body) environment)) := by
  intro proposed
  rcases proposed with classical | restart
  · exact singleGate_notClassical (allowAllocation := allowAllocation)
      body coordinate trace classical
  · exact singleGate_noRestart (allowAllocation := allowAllocation) environment
      body coordinate trace restart

end QuantumAlg.Circuit
