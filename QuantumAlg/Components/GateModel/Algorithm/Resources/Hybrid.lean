/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.GateModel.Algorithm.Resources.Events

/-!
# Complete hybrid allowances with independent native gate limits

Filtering an independent finite component allowance removes only native gate
coordinates. Preparation, measurement, classical operations and service events
retain their literal labels. A separate proved gate limit can then sharpen
the complete pool without inferring finite support from a scalar work count.
-/

namespace QuantumAlg.AlgorithmGate

noncomputable section

attribute [local instance] Classical.propDecidable

variable {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The actual event kinds outside the three native gate coordinates. -/
def nonGateEvent : Resource.Event (.quantum model .empty operations services) → Prop
  | .gate _ => False
  | _ => True

/-- Remove native gates from a finite allowance, retaining every other literal event label. -/
def nonGateEnvelope (pool : ResourcePool (.quantum model .empty operations services)) :
    ResourcePool (.quantum model .empty operations services) := by
  classical
  exact pool.filter nonGateEvent

/-- Filtering independent component allowances respects literal pool addition. -/
lemma nonGateEnvelope_add
    (first second : ResourcePool (.quantum model .empty operations services)) :
    nonGateEnvelope (first + second) = nonGateEnvelope first + nonGateEnvelope second := by
  classical
  exact Multiset.filter_add _ _ _

/-- A complete component bound also bounds all its nongate coordinates. -/
lemma nonGateEnvelope_mono {first second : ResourcePool (.quantum model .empty operations services)}
    (bounded : first ≤ second) : nonGateEnvelope first ≤ nonGateEnvelope second := by
  classical
  exact Multiset.filter_le_filter _ bounded

/-- The finite filter preserves the multiplicity of every retained coordinate exactly. -/
lemma count_nonGateEnvelope (pool : ResourcePool (.quantum model .empty operations services))
    (event : Resource.Event (.quantum model .empty operations services)) :
    ResourcePool.count event (nonGateEnvelope pool) =
      if nonGateEvent event then ResourcePool.count event pool else 0 := by
  classical
  exact Multiset.count_filter

/-- An oracle-free pure word has no classical, preparation, or measurement events. -/
lemma nonGateEnvelope_unitary {count : Nat} {layout : QuantumLayout count}
    (body : UnitaryCircuit model .empty layout) :
    nonGateEnvelope (body.eventCost operations services) = 0 := by
  classical
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (nonGateEnvelope (body.eventCost operations services)) =
    ResourcePool.count event 0
  rw [count_nonGateEnvelope, ResourcePool.count_zero]
  cases event with
  | oracle impossible => cases impossible
  | gate coordinate => simp [nonGateEvent]
  | classicalOperation coordinate =>
      simpa [nonGateEvent] using UnitaryCircuit.unitaryCircuit_event_count_classical_context
        body operations services (.classicalOperation coordinate)
  | classicalQuery coordinate =>
      simpa [nonGateEvent] using UnitaryCircuit.unitaryCircuit_event_count_classical_context
        body operations services (.classicalQuery coordinate)
  | preparation dimension =>
      simpa [nonGateEvent] using UnitaryCircuit.unitaryCircuit_event_count_classical_context
        body operations services (.preparation dimension)
  | measurement dimension =>
      simpa [nonGateEvent] using UnitaryCircuit.unitaryCircuit_event_count_classical_context
        body operations services (.measurement dimension)

/-- Separate proved gate limits and a complete finite nongate allowance bound the whole pool. -/
lemma complete_pool_le (pool other : ResourcePool (.quantum model .empty operations services))
    (single cnot toffoli : Nat)
    (gates : ∀ coordinate, ResourcePool.count (.gate coordinate) pool ≤ match coordinate with
      | .singleQubit => single | .cnot => cnot | .toffoli => toffoli)
    (rest : nonGateEnvelope pool ≤ nonGateEnvelope other) :
    pool ≤ gateEnvelope operations services single cnot toffoli + nonGateEnvelope other := by
  classical
  apply ResourcePool.le_iff_count.mpr
  intro event
  have remaining := ResourcePool.le_iff_count.mp rest event
  rw [ResourcePool.count_add]
  rw [count_nonGateEnvelope, count_nonGateEnvelope] at remaining
  cases event with
  | oracle impossible => cases impossible
  | gate coordinate =>
      rw [count_gateEnvelope, count_nonGateEnvelope]
      cases coordinate with
      | singleQubit => simpa [nonGateEvent] using gates .singleQubit
      | cnot => simpa [nonGateEvent] using gates .cnot
      | toffoli => simpa [nonGateEvent] using gates .toffoli
  | classicalOperation coordinate =>
      simpa [gateEnvelope, count_nonGateEnvelope, nonGateEvent] using remaining
  | classicalQuery coordinate =>
      simpa [gateEnvelope, count_nonGateEnvelope, nonGateEvent] using remaining
  | preparation dimension =>
      simpa [gateEnvelope, count_nonGateEnvelope, nonGateEvent] using remaining
  | measurement dimension =>
      simpa [gateEnvelope, count_nonGateEnvelope, nonGateEvent] using remaining

end

end QuantumAlg.AlgorithmGate
