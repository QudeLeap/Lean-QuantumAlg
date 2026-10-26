/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm.Resources
import all QuantumAlg.Components.GateModel.Algorithm.Resources
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete independent native allowance for oracle-free unitary words

Three independent gate limits bound every actual event of an oracle-free
word in any surrounding classical operation and service model. Classical
operations, queries, preparation and measurements are absent by the existing
unitary accounting law, rather than silently omitted from the comparison.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- The three independent native gate limits, with no other event coordinate. -/
public def gateEnvelope (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (single cnot toffoli : Nat) : ResourcePool (.quantum model .empty operations services) :=
  ResourcePool.singleton (model := .quantum model .empty operations services)
    (.gate .singleQubit) single +
    (ResourcePool.singleton (model := .quantum model .empty operations services)
      (.gate .cnot) cnot +
      ResourcePool.singleton (model := .quantum model .empty operations services)
        (.gate .toffoli) toffoli)

/-- Each native coordinate reads exactly its independently supplied multiplicity. -/
public lemma count_gateEnvelope (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (single cnot toffoli : Nat) (coordinate : Coordinate) :
    ResourcePool.count (model := .quantum model .empty operations services)
      (.gate coordinate) (gateEnvelope operations services single cnot toffoli) =
      match coordinate with
      | .singleQubit => single | .cnot => cnot | .toffoli => toffoli := by
  cases coordinate <;> simp [gateEnvelope, Resource.Event.gate.injEq]

/-- Independent gate limits bound the complete actual pool in every classical context. -/
public lemma algorithmGate_unitary_pool_le {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit model .empty layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (single cnot toffoli : Nat)
    (bounded : ∀ coordinate, ResourcePool.count (model := .quantum model .empty)
      (.gate coordinate) body.eventCost ≤ match coordinate with
        | .singleQubit => single | .cnot => cnot | .toffoli => toffoli) :
    body.eventCost operations services ≤ gateEnvelope operations services single cnot toffoli := by
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | oracle impossible => cases impossible
  | gate coordinate =>
      rw [count_gateEnvelope]
      exact bounded coordinate
  | classicalOperation coordinate => exact Nat.zero_le _
  | classicalQuery coordinate => exact Nat.zero_le _
  | preparation dimension => exact Nat.zero_le _
  | measurement dimension => exact Nat.zero_le _

/-- The same complete gate allowance applies to the actual hybrid unitary constructor. -/
public lemma algorithmGate_unitaryCircuit_pool_le
    {ctx : RuntimeCtx .quantum} {allocate : Bool}
    (body : UnitaryCircuit model .empty ctx.quantumLayout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (single cnot toffoli : Nat)
    (bounded : ∀ coordinate, ResourcePool.count (model := .quantum model .empty)
      (.gate coordinate) body.eventCost ≤ match coordinate with
        | .singleQubit => single | .cnot => cnot | .toffoli => toffoli)
    (path : (Circuit.unitary (operations := operations) (classicalOracles := services)
      (allowAllocation := allocate) body).Path) :
    (Circuit.unitary (operations := operations) (classicalOracles := services)
      (allowAllocation := allocate) body).resourcePool path ≤
      gateEnvelope operations services single cnot toffoli := by
  change ResourcePool.ofList (body.eventTrace operations services) ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost body operations services]
  exact algorithmGate_unitary_pool_le body operations services single cnot toffoli bounded

end

end QuantumAlg.AlgorithmGate
