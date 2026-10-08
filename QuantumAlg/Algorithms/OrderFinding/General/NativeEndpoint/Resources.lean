/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Resources
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Depth

/-!
# Complete native general order-finding event and depth limits

An independent coordinate pool adds the source sample's actual preparation,
native gates, query, Z writes and packing to the finite classical recovery
allowance. The depth bound follows the same sequential code and includes
the whole source sample before dependent recovery.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

/-- Independent event envelope for the actual source sample and finite recovery. -/
def eventBudget {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    ResourcePool (Sampling.Native.Framed.model access) :=
  Sampling.Native.eventBudget access +
    ClassicalRoutines.OrderRecovery.Native.eventEnvelope
      (Sampling.Native.Framed.model access) width t

/-- Independent full sample-plus-recovery unit-event depth allowance. -/
def depthBudget (t width : Nat) : Nat :=
  Sampling.Native.depthBudget t width +
    ClassicalRoutines.OrderRecovery.Native.unitDepthBound width t

/-- Every executed path fits the independently specified selected-model event pool. -/
theorem code_events_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) (path : (code hinput access).Path) :
    (code hinput access).resourcePool path ≤ eventBudget access := by
  change ResourcePool.ofList ((SourceNativeSampling.code access).eventTrace path.1 ++
    (recoveryCode hinput access).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (SourceNativeSampling.code access).resourcePool path.1 +
    (recoveryCode hinput access).resourcePool path.2.2 ≤ _
  rw [SourceNativeSampling.events]
  exact add_le_add le_rfl
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (model := Sampling.Native.Framed.model access)
      (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
      (resultRef t width) path.2.2)

/-- The complete path's sequential depth includes source sampling and recovery. -/
theorem code_depth_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) (path : (code hinput access).Path) :
    (code hinput access).depth (fun _ => 1) path ≤ depthBudget t width := by
  change (SourceNativeSampling.code access).depth (fun _ => 1) path.1 +
    (0 + (recoveryCode hinput access).depth (fun _ => 1) path.2.2) ≤ _
  rw [Nat.zero_add, SourceNativeSampling.depth]
  exact Nat.add_le_add_left
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_unitDepth_le
      (model := Sampling.Native.Framed.model access)
      (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
      (resultRef t width) path.2.2) _

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
