/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
public import QuantumAlg.Util.Order.Finding
public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
import all QuantumAlg.Components.Classical.OrderRecovery.Native.ClassicalCounts
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Classical-operation count of complete native general order finding

The source sampler packs one phase word. The finite recovery allowance counts
decoding, loading, candidate visits, modular validation and result packing.
The independent budget bounds every actual path, including failed samples.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

private theorem sampling_classicalCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Sampling.Native.eventBudget access) = 1 := by
  simp [Sampling.Native.eventBudget, Sampling.Native.unitaryBudget,
    Resource.Event.classicalOperationWeight]

private theorem eventBudget_classicalCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventBudget access) =
      4 * (t + 1) + 5 +
        2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) := by
  rw [eventBudget, ResourcePool.weightedCount_add, sampling_classicalCount,
    ClassicalRoutines.OrderRecovery.Native.eventEnvelope_classicalCount]
  omega

/-- The problem's independent event allowance has an explicit classical weight. -/
public theorem generalOrderFinding_problem_classicalOperations {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (problem hinput access).resources.events =
      4 * (t + 1) + 5 +
        2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) :=
  eventBudget_classicalCount access

/-- Every path of the same public algorithm fits the classical-operation allowance. -/
public theorem generalOrderFinding_algorithm_classicalOperations_le {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm hinput access).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm hinput access).run.code.resourcePool path) ≤
      4 * (t + 1) + 5 +
        2 * (t + 1) * (2 * width + 18 + 6 * (t + 1)) := by
  have bounded := ResourcePool.weightedCount_mono
    Resource.Event.classicalOperationWeight (code_events_le hinput access path)
  exact bounded.trans_eq (eventBudget_classicalCount access)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
