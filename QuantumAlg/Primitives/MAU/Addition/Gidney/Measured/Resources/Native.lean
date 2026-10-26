/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Native gate-word coordinates in the surrounding hybrid model

The classical operation and service grants do not alter the addressed native
instructions. Every count below is taken from the actual compiled gate word,
with the caller's operation and service models retained.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.NativeResources

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- One literal source instruction's actual coordinate in the full surrounding execution model. -/
def event : GateSpec encoding →
    Resource.Event (.quantum AlgorithmGate.model oracles operations services)
  | .x _ => .gate .singleQubit
  | .cnot _ _ _ => .gate .cnot
  | .toffoli _ _ _ _ _ _ => .gate .toffoli

/-- The actual primitive retains its declaration-owned coordinate with every classical grant. -/
lemma gate_eventCost (physical : QubitLayout encoding.width) (gate : GateSpec encoding) :
    (gate.program physical oracles).eventCost operations services =
      ResourcePool.singleton (event (oracles := oracles) (operations := operations)
        (services := services) gate) := by
  cases gate <;> rfl

/-- Every coordinate count is computed from the same actual native word in the hybrid model. -/
lemma word_count (physical : QubitLayout encoding.width) (gates : List (GateSpec encoding))
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles operations services)) :
    ResourcePool.count focus ((programList physical oracles gates).eventCost operations services) =
      (gates.map fun gate => if event gate = focus then 1 else 0).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change ResourcePool.count focus
        ((gate.program physical oracles).eventCost operations services +
          (programList physical oracles rest).eventCost operations services) = _
      rw [ResourcePool.count_add, gate_eventCost, ih]
      simp only [List.map_cons, List.sum_cons, ResourcePool.count_singleton]

/-- The complete hybrid instruction model retains the actual source Toffoli multiplicity. -/
lemma word_toffoli_count (physical : QubitLayout encoding.width)
    (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .toffoli) ((programList physical oracles gates).eventCost operations services) =
      (gates.map toffoliMultiplicity).sum := by
  rw [word_count]
  apply congrArg List.sum
  apply List.map_congr_left
  intro gate _
  cases gate <;> simp [event, toffoliMultiplicity]

/-- CNOT conjugations remain distinct from every source Toffoli. -/
lemma word_cnot_count (physical : QubitLayout encoding.width)
    (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .cnot) ((programList physical oracles gates).eventCost operations services) =
      (gates.map cnotMultiplicity).sum := by
  rw [word_count]
  apply congrArg List.sum
  apply List.map_congr_left
  intro gate _
  cases gate <;> simp [event, cnotMultiplicity]

/-- Source X gates contribute their exact actual single-qubit multiplicity. -/
lemma word_singleQubit_count (physical : QubitLayout encoding.width)
    (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.gate .singleQubit) ((programList physical oracles gates).eventCost operations services) =
      (gates.map xMultiplicity).sum := by
  rw [word_count]
  apply congrArg List.sum
  apply List.map_congr_left
  intro gate _
  cases gate <;> simp [event, xMultiplicity]

/-- The native X/CNOT/Toffoli word performs no physical measurement. -/
lemma word_measurement_count (physical : QubitLayout encoding.width)
    (gates : List (GateSpec encoding)) (dimension : ℕ+) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles operations services)
        (.measurement dimension)
        ((programList physical oracles gates).eventCost operations services) = 0 := by
  rw [word_count]
  apply List.sum_eq_zero
  intro value member
  rcases List.mem_map.mp member with ⟨gate, _, rfl⟩
  cases gate <;> simp [event]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.NativeResources
