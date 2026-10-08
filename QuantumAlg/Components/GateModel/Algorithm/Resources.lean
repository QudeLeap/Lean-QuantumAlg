/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Components.GateModel.Algorithm
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting

/-! # Scalar cardinality of an actual oracle-free default-model unitary word -/

namespace QuantumAlg.AlgorithmGate

noncomputable section

/-- Every literal event in an oracle-free unitary word belongs to one of
the three native coordinates. No circuit or repetition is expanded. -/
public theorem algorithmGate_unitaryEventCost_eq_counts {count : Nat}
    {layout : QuantumLayout count} (body : UnitaryCircuit model .empty layout) :
    body.eventCost =
      ResourcePool.singleton (model := .quantum model .empty) (.gate Coordinate.singleQubit)
          (ResourcePool.count (model := .quantum model .empty)
            (.gate Coordinate.singleQubit) body.eventCost) +
        ResourcePool.singleton (model := .quantum model .empty) (.gate Coordinate.cnot)
          (ResourcePool.count (model := .quantum model .empty)
            (.gate Coordinate.cnot) body.eventCost) +
        ResourcePool.singleton (model := .quantum model .empty) (.gate Coordinate.toffoli)
          (ResourcePool.count (model := .quantum model .empty)
            (.gate Coordinate.toffoli) body.eventCost) := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event body.eventCost = _
  cases event with
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | oracle impossible => cases impossible
  | gate coordinate =>
      cases coordinate <;>
        simp [ResourcePool.singleton, ResourcePool.count, Multiset.count_replicate]
  | preparation dimension =>
      have zero := UnitaryCircuit.unitaryCircuit_event_count_classical_context body
        .empty .empty (.preparation dimension)
      simpa [ResourcePool.singleton, ResourcePool.count, Multiset.count_replicate] using zero
  | measurement dimension =>
      have zero := UnitaryCircuit.unitaryCircuit_event_count_classical_context body
        .empty .empty (.measurement dimension)
      simpa [ResourcePool.singleton, ResourcePool.count, Multiset.count_replicate] using zero

/-- The total literal count is the sum of the same word's native gate counts. -/
public theorem algorithmGate_unitaryEventCost_card {count : Nat}
    {layout : QuantumLayout count} (body : UnitaryCircuit model .empty layout) :
    body.eventCost.card =
      ResourcePool.count (model := .quantum model .empty)
        (.gate Coordinate.singleQubit) body.eventCost +
        ResourcePool.count (model := .quantum model .empty)
        (.gate Coordinate.cnot) body.eventCost +
        ResourcePool.count (model := .quantum model .empty)
        (.gate Coordinate.toffoli) body.eventCost := by
  conv_lhs => rw [algorithmGate_unitaryEventCost_eq_counts body]
  simp [ResourcePool.singleton]

end

end QuantumAlg.AlgorithmGate
