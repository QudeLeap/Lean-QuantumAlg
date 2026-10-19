/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Refinement
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Components.Gates.Toffoli.Resources
import Mathlib.Data.Multiset.Bind

/-!
# Exact event pools after native Toffoli substitution

Only a Toffoli event is replaced: its executed word contributes nine arbitrary
single-qubit gates and six CNOTs. Other events keep their original coordinates.
The pool transformation is proved against the actual substituted circuit.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def replaceEvent (oracles : OracleModel) :
    Resource.Event (.quantum AlgorithmGate.model oracles) →
      ResourcePool (.quantum AlgorithmGate.model oracles)
  | .gate .toffoli =>
      9 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) +
        6 • ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .cnot)
  | event => ResourcePool.singleton event

/-- Literal additive substitution of the events emitted by each replacement word. -/
def expandedBudget (oracles : OracleModel) :
    ResourcePool (.quantum AlgorithmGate.model oracles) →+
      ResourcePool (.quantum AlgorithmGate.model oracles) where
  toFun pool := pool.bind (replaceEvent oracles)
  map_zero' := Multiset.zero_bind _
  map_add' _ _ := Multiset.add_bind _ _ _

private lemma expandedBudget_singleton (oracles : OracleModel)
    (event : Resource.Event (.quantum AlgorithmGate.model oracles)) :
    expandedBudget oracles (ResourcePool.singleton event) = replaceEvent oracles event := by
  simp [expandedBudget, ResourcePool.singleton]

private lemma nativeExpansion_cost (oracles : OracleModel) {count : Nat}
    {ambient : QuantumLayout count}
    (application : GateModel.Application AlgorithmGate.model ambient) :
    (nativeExpansion oracles application).circuit.eventCost =
      expandedBudget oracles (ResourcePool.singleton (.gate application.coordinate)) := by
  rw [expandedBudget_singleton]
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token with
  | toffoli =>
      change (UnitaryCircuit.placeAt _ _ _ _ (circuit oracles)).eventCost = _
      rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
        UnitaryCircuit.placeAt_eventTrace, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
        toffoliExpansion_eventCost]
      rfl
  | cnot => rfl
  | singleQubit operator => rfl

/-- The event ledger is computed from the same expansion whose full matrix is preserved. -/
lemma toffoliExpansion_expanded_eventCost {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    (expand source).eventCost = expandedBudget oracles source.eventCost := by
  apply UnitaryCircuit.refine_eventCost (expansionInstructions oracles) (expandedBudget oracles)
  · exact nativeExpansion_cost oracles
  · intro width layout application
    rw [expandedBudget_singleton]
    rfl

end
end QuantumAlg.Gate.Toffoli
