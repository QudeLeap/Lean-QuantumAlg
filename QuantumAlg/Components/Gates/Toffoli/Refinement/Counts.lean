/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Refinement.Resources
import all QuantumAlg.Components.Gates.Toffoli.Refinement
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Coordinate counts of the actual Toffoli expansion

Each source Toffoli contributes nine single-qubit gates and six CNOTs. The
expanded construction has no Toffoli occurrence, and every oracle coordinate
retains exactly its original count.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def replacementCount : AlgorithmGate.Coordinate → Nat
  | .toffoli => 0
  | .cnot => 6
  | .singleQubit => 9

private lemma replacement_native_count (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles))
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate coordinate) (replaceEvent oracles event) =
      (if coordinate = .toffoli then 0 else ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles) (.gate coordinate)
        (ResourcePool.singleton event)) +
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) (ResourcePool.singleton event) * replacementCount coordinate := by
  cases event with
  | classicalOperation impossible => cases impossible
  | classicalQuery impossible => cases impossible
  | gate gate => cases gate <;> cases coordinate <;> simp [replaceEvent, replacementCount]
  | oracle query => cases coordinate <;> simp [replaceEvent, replacementCount]
  | preparation dimension => cases coordinate <;> simp [replaceEvent, replacementCount]
  | measurement dimension => cases coordinate <;> simp [replaceEvent, replacementCount]

private lemma expanded_native_count (oracles : OracleModel)
    (pool : ResourcePool (.quantum AlgorithmGate.model oracles))
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate coordinate) (expandedBudget oracles pool) =
      (if coordinate = .toffoli then 0 else ResourcePool.count
        (model := .quantum AlgorithmGate.model oracles) (.gate coordinate) pool) +
        ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli) pool *
          replacementCount coordinate := by
  induction pool using Multiset.induction_on with
  | empty => simp
  | cons event pool ih =>
      have consPool : event ::ₘ pool = ResourcePool.singleton event + pool := by
        simp [ResourcePool.singleton]
      rw [consPool, map_add, ResourcePool.count_add, expandedBudget_singleton,
        replacement_native_count, ih]
      simp only [ResourcePool.count_add, Nat.add_mul]
      split_ifs <;> omega

/-- Single-qubit counts include all nine single-qubit gates in each actual Toffoli word. -/
lemma toffoliExpansion_expanded_singleQubit_count {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .singleQubit)
      (expand source).eventCost =
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .singleQubit) source.eventCost +
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) source.eventCost * 9 := by
  rw [toffoliExpansion_expanded_eventCost]
  exact expanded_native_count oracles source.eventCost .singleQubit

/-- Every expanded Toffoli adds exactly six CNOTs to the original CNOT occurrences. -/
lemma toffoliExpansion_expanded_cnot_count {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
      (expand source).eventCost =
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .cnot) source.eventCost +
      ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
        (.gate .toffoli) source.eventCost * 6 := by
  rw [toffoliExpansion_expanded_eventCost]
  exact expanded_native_count oracles source.eventCost .cnot

/-- No native Toffoli remains anywhere in the substituted construction. -/
lemma toffoliExpansion_expanded_toffoli_count {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.gate .toffoli)
      (expand source).eventCost = 0 := by
  rw [toffoliExpansion_expanded_eventCost]
  simpa [replacementCount] using expanded_native_count oracles source.eventCost .toffoli

end
end QuantumAlg.Gate.Toffoli
