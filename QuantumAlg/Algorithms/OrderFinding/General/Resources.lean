/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Resources
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Depth

/-!
# Actual native general order-finding event and depth bounds

The same full execution includes the original source sample and every real
classical recovery instruction. Resource limits are declared from the source
widths and retain their native operation coordinates.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

/-- Original quantum source budget followed by the independent finite recovery allowance. -/
def eventBudget (N x t width : Nat) : ResourcePool .quantum :=
  Sampling.eventBudget N x t width +
    ClassicalRoutines.OrderRecovery.Native.eventEnvelope .quantum width t

/-- Original source dependency depth followed by actual finite recovery depth. -/
def depthBudget (t width : Nat) : Nat :=
  Sampling.depthBudget t + ClassicalRoutines.OrderRecovery.Native.unitDepthBound width t

/-- Every actual full path fits the fixed native-coordinate source and recovery budget. -/
theorem code_events_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (path : (code hinput A).Path) :
    (code hinput A).resourcePool path ≤ eventBudget N x t width := by
  change ResourcePool.ofList ((NativeSampling.code A).eventTrace path.1 ++
    (recoveryCode hinput A).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (NativeSampling.code A).resourcePool path.1 +
    (recoveryCode hinput A).resourcePool path.2.2 ≤ _
  rw [NativeSampling.events]
  exact add_le_add le_rfl
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (recoverySpec hinput A) (baseInput t width) (sampleInput t width) (resultRef t width)
      path.2.2)

/-- The actual sample and dependent recovery share the same complete serial depth ledger. -/
theorem code_depth_le {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (path : (code hinput A).Path) :
    (code hinput A).depth (fun _ => 1) path ≤ depthBudget t width := by
  change (NativeSampling.code A).depth (fun _ => 1) path.1 +
    (0 + (recoveryCode hinput A).depth (fun _ => 1) path.2.2) ≤ _
  rw [Nat.zero_add, NativeSampling.depth]
  exact Nat.add_le_add_left
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_unitDepth_le
      (recoverySpec hinput A) (baseInput t width) (sampleInput t width) (resultRef t width)
      path.2.2) _

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
