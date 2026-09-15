/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Endpoint
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.OrderFinding.General.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Algorithms.OrderFinding.General.Specification
import all QuantumAlg.Algorithms.OrderFinding.General.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Algorithms.OrderFinding.Construction
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Components.Classical.OrderRecovery.Native.ClassicalCounts
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Explicit classical-operation bounds for complete general order finding

The numerical limit is the classical weight of the existing native event
budget. Sampling contributes its one real bit-packing operation. Recovery
contributes its actual decoder, constant loading, bounded candidate visits,
modular validations and option packing. The same limit bounds every actual
path of the public algorithm, including paths outside the success event.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint

noncomputable section

private theorem sampling_classicalCount (N x t width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Sampling.eventBudget N x t width) = 1 := by
  simp [Sampling.eventBudget, Sampling.unitaryEventBudget, Sampling.basisPreparationEvent,
    modExpEvent, WalshHadamard.hadamardEvent, Resource.Event.classicalOperationWeight]

private theorem eventBudget_classicalCount (N x t width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (NativeEndpoint.eventBudget N x t width) =
      4 * (t + 1) + 5 + 2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) := by
  rw [NativeEndpoint.eventBudget, ResourcePool.weightedCount_add, sampling_classicalCount,
    ClassicalRoutines.OrderRecovery.Native.eventEnvelope_classicalCount]
  omega

/-- The independent event allowance has this explicit total classical-operation weight. -/
public theorem problem_classicalOperations {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (problem hinput A).resources.events =
      4 * (t + 1) + 5 + 2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) :=
  eventBudget_classicalCount N x t width

/-- Every actual full algorithm path satisfies the explicit classical-operation bound. -/
public theorem algorithm_classicalOperations_le {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (algorithm hinput A).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm hinput A).run.code.resourcePool path) ≤
      4 * (t + 1) + 5 + 2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) := by
  have bounded := ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (NativeEndpoint.code_events_le hinput A path)
  exact bounded.trans_eq (eventBudget_classicalCount N x t width)

end

end QuantumAlg.OrderFinding.ShorSourceJoint
