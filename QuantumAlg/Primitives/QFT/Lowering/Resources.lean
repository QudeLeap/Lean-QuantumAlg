/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Primitives.QFT.Lowering
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.ControlledPhase.Semantics
import all QuantumAlg.Components.Gates.Swap
import Mathlib.Data.Multiset.Bind

/-! # Exact resource substitution for the actual Fourier lowering -/

namespace QuantumAlg.QuantumFourierTransform.Lowering
noncomputable section

/-- The event word executed by each source instruction. -/
public def replacementEvents (oracles : OracleModel) :
    Resource.Event (.quantum FourierGate.model .empty) →
      ResourcePool (.quantum AlgorithmGate.model oracles)
  | .gate .hadamard => ResourcePool.singleton (.gate .singleQubit)
  | .gate .controlledPhase =>
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) 3 +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) 2
  | .gate .swap => ResourcePool.singleton (.gate .cnot) 3
  | .oracle impossible => nomatch impossible
  | .classicalOperation impossible => nomatch impossible
  | .classicalQuery impossible => nomatch impossible
  | .preparation dimension => ResourcePool.singleton (.preparation dimension)
  | .measurement dimension => ResourcePool.singleton (.measurement dimension)

/-- An additive map justified below against each executed replacement word. -/
public def expandedBudget (oracles : OracleModel) :
    ResourcePool (.quantum FourierGate.model .empty) →+
      ResourcePool (.quantum AlgorithmGate.model oracles) where
  toFun pool := pool.bind (replacementEvents oracles)
  map_zero' := Multiset.zero_bind _
  map_add' _ _ := Multiset.add_bind _ _ _

/-- One source event expands to its actual replacement word. -/
public lemma expandedBudget_singleton (oracles : OracleModel)
    (event : Resource.Event (.quantum FourierGate.model .empty)) :
    expandedBudget oracles (ResourcePool.singleton event) = replacementEvents oracles event := by
  simp [expandedBudget, ResourcePool.singleton]

/-- Repeating one source event repeats the replacement word's resource pool. -/
public lemma expandedBudget_singleton_multiplicity (oracles : OracleModel)
    (event : Resource.Event (.quantum FourierGate.model .empty)) (multiplicity : Nat) :
    expandedBudget oracles (ResourcePool.singleton event multiplicity) =
      multiplicity • replacementEvents oracles event := by
  induction multiplicity with
  | zero => exact map_zero _
  | succ multiplicity ih =>
      change expandedBudget oracles
        (ResourcePool.singleton event + ResourcePool.singleton event multiplicity) = _
      rw [map_add, expandedBudget_singleton, ih, succ_nsmul]
      exact add_comm _ _

private lemma nativeRealization_cost (oracles : OracleModel) {count : Nat}
    {layout : QuantumLayout count} (application : GateModel.Application FourierGate.model layout) :
    (nativeRealization oracles application).circuit.eventCost =
      expandedBudget oracles (ResourcePool.singleton (.gate application.coordinate)) := by
  rw [expandedBudget_singleton]
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  change (UnitaryCircuit.placeAt _ _ _ _ (localRealization oracles token).circuit).eventCost = _
  rw [UnitaryCircuit.placeAt_eventCost, ← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  cases token with
  | hadamard => rfl
  | controlledPhase angle =>
      change ResourcePool.ofList (Gate.ControlledPhase.circuit oracles angle).eventTrace =
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
          (.gate .singleQubit) 3 +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles) (.gate .cnot) 2
      rw [Gate.ControlledPhase.controlledPhase_circuit_events]
      apply Multiset.ext.mpr
      intro event
      change ResourcePool.count event _ = ResourcePool.count event _
      rw [ResourcePool.count_add, ResourcePool.count_singleton,
        ResourcePool.count_singleton, ResourcePool.count_ofList]
      simp only [List.count_cons, List.count_nil, beq_iff_eq]
      split_ifs <;> omega
  | swap => rfl

/-- The same compiled circuit has exactly the additive expansion of its source ledger. -/
public lemma lower_eventCost (oracles : OracleModel) {count : Nat}
    {layout : QuantumLayout count} (source : UnitaryCircuit FourierGate.model .empty layout) :
    (lower oracles source).eventCost = expandedBudget oracles source.eventCost := by
  apply UnitaryCircuit.refine_eventCost (instructions oracles) (expandedBudget oracles)
  · exact nativeRealization_cost oracles
  · intro width ambient application
    exact False.elim (OracleModel.Occurrence.no_empty_oracle_occurrence application.occurrence)

end
end QuantumAlg.QuantumFourierTransform.Lowering
