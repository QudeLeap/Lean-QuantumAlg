/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources

/-!
# Every native gate coordinate of the actual short-DLP member

The interface quantifies over the complete gate label, including its control
dimensions. It is a projection of the proved strict native pool relation,
so it neither identifies distinct control layers nor replaces their costs
by an uncontrolled Toffoli coordinate.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

/-- Every complete native gate label obeys its own independent coordinate budget. -/
theorem compiledCircuit_eventGateCount_le_envelope (m ell width N : Nat)
    (g x : (ZMod N)ˣ) (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) (compiledCircuit m ell width N g x).eventCost ≤
      ResourcePool.count (.gate label) (compiledCircuitEventEnvelope m ell width N) := by
  change Multiset.count (Resource.Event.gate label)
      (compiledCircuit m ell width N g x).eventCost ≤
    Multiset.count (Resource.Event.gate label) (compiledCircuitEventEnvelope m ell width N)
  exact Multiset.count_le_of_le (Resource.Event.gate label)
    (compiledCircuit_eventCost_le m ell width N g x)

/-- Every coordinate cap is bounded by the independent full pool's closed cardinality. -/
theorem compiledCircuitEventEnvelope_gateCount_le_polynomial (m ell width N : Nat)
    (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) (compiledCircuitEventEnvelope m ell width N) ≤
      polynomialPrimitiveBound m ell width N :=
  (Multiset.count_le_card _ _).trans_eq (compiledCircuitEventEnvelope_card m ell width N)

/-- The actual occurrence count of any native label satisfies the full pool's closed bound. -/
theorem compiledCircuit_eventGateCount_le_polynomial (m ell width N : Nat)
    (g x : (ZMod N)ˣ) (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) (compiledCircuit m ell width N g x).eventCost ≤
      polynomialPrimitiveBound m ell width N :=
  (compiledCircuit_eventGateCount_le_envelope m ell width N g x label).trans
    (compiledCircuitEventEnvelope_gateCount_le_polynomial m ell width N label)

/-- Actual coordinate occurrences also satisfy the tighter total-occurrence bound. -/
theorem compiledCircuit_eventGateCount_le_actual_bound (m ell width N : Nat)
    (g x : (ZMod N)ˣ) (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) (compiledCircuit m ell width N g x).eventCost ≤
      compiledCircuitActualEventBound m ell width :=
  (Multiset.count_le_card _ _).trans (compiledCircuit_actual_event_bound m ell width N g x)

end

end QuantumAlg.ShortDLP.CompiledMAU
