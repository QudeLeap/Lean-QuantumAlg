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
# Preserving every granted oracle query through Toffoli expansion

The substitution changes only native gate occurrences. Ordinary, inverse,
controlled and controlled-inverse queries remain distinct coordinates of the
original oracle model, and every coordinate keeps its exact multiplicity.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private theorem expanded_query_count (oracles : OracleModel)
    (pool : ResourcePool (.quantum AlgorithmGate.model oracles))
    (coordinate : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.oracle coordinate) (expandedBudget oracles pool) =
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.oracle coordinate) pool := by
  induction pool using Multiset.induction_on with
  | empty => simp [expandedBudget]
  | cons event pool ih =>
      cases event with
      | classicalOperation impossible => cases impossible
      | classicalQuery impossible => cases impossible
      | gate gate =>
          cases gate <;>
            simp_all [expandedBudget, replaceEvent, ResourcePool.count,
              ResourcePool.singleton]
      | oracle query =>
          simp_all [expandedBudget, replaceEvent, ResourcePool.count,
            ResourcePool.singleton, Multiset.count_cons]
      | preparation dimension =>
          simp_all [expandedBudget, replaceEvent, ResourcePool.count,
            ResourcePool.singleton]
      | measurement dimension =>
          simp_all [expandedBudget, replaceEvent, ResourcePool.count,
            ResourcePool.singleton]

/-- The actual expanded circuit retains exactly every original query coordinate count. -/
theorem toffoliExpansion_preserves_query_count {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient)
    (coordinate : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.oracle coordinate) (expand source).eventCost =
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.oracle coordinate) source.eventCost := by
  rw [toffoliExpansion_expanded_eventCost]
  exact expanded_query_count oracles source.eventCost coordinate

end
end QuantumAlg.Gate.Toffoli
