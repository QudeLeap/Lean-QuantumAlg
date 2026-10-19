/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Primitives.ZReset.Resources
import all QuantumAlg.Primitives.ZReset.Bank

/-!
# Full event observations of the actual declared ECDLP recovery execution

The original query word contributes only quantum events. Every real checked
attempt and the sole final optional packing instruction retain their actual
classical weight. Both full resets are charged in every prescribed round.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Quantum coordinates receive only initialization and the unchanged actual sampling rounds. -/
public lemma whole_budget_nonclassical_count (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (event : Resource.Event (Sampling.executionModel I))
    (outside : ∀ label, event ≠ .classicalOperation label) :
    ResourcePool.count event (eventBudget I expansion nontrivial count) =
      ResourcePool.count event (initializationBudget I) +
        count * ResourcePool.count event (Sampling.Reuse.eventBudget I expansion) := by
  have checking := attemptEnvelope_count_eq_zero event outside (curve E) (modulus I nontrivial)
  simp only [eventBudget, tailEventBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.count_add, ResourcePool.count_scale, checking, add_zero]
  simp [ResourcePool.count, ResourcePool.ofList, outside]

private lemma pure_classical_weight_zero {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {layout : QuantumLayout count} (body : UnitaryCircuit gates oracles layout) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (body.eventCost BitWord.model .empty) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event member
  cases event with
  | classicalOperation label =>
      have absent : ResourcePool.count
          (model := .quantum gates oracles BitWord.model .empty) (.classicalOperation label)
          (body.eventCost BitWord.model .empty) = 0 :=
        UnitaryCircuit.unitaryCircuit_event_count_classical_context
          body BitWord.model .empty (.classicalOperation label)
      have positive := Multiset.count_pos.mpr member
      change 0 < ResourcePool.count (.classicalOperation label)
        (body.eventCost BitWord.model .empty) at positive
      rw [absent] at positive
      omega
  | classicalQuery impossible => cases impossible
  | gate _ => rfl
  | oracle _ => rfl
  | preparation _ => rfl
  | measurement _ => rfl

/-- Sampling emits no classical instructions; actual checked attempts and final packing do. -/
lemma whole_budget_classical_count (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (eventBudget I expansion nontrivial count) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (initializationBudget I) +
        count * ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (attemptEnvelope (Sampling.executionModel I) (curve E) (modulus I nontrivial)) + 1 := by
  simp only [eventBudget, tailEventBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.scale, Sampling.Reuse.eventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, pure_classical_weight_zero]
  simp [Resource.Event.classicalOperationWeight]
  ring

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
