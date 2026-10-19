/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.Space

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
public def eventBudget (t width : Nat) :
    ResourcePool (Sampling.Native.Framed.model t width) :=
  Sampling.Native.eventBudget t width +
    ClassicalRoutines.OrderRecovery.Native.eventEnvelope
      (Sampling.Native.Framed.model t width) width t

/-- Independent full sample-plus-recovery unit-event depth allowance. -/
public def depthBudget (t width : Nat) : Nat :=
  Sampling.Native.depthBudget t width +
    ClassicalRoutines.OrderRecovery.Native.unitDepthBound width t

/-- Every executed path fits the independently specified selected-model event pool. -/
lemma code_events_le {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) (path : (code spec t).Path) :
    (code spec t).resourcePool path ≤ eventBudget t width := by
  change ResourcePool.ofList ((SourceNativeSampling.code t width).eventTrace path.1 ++
    (recoveryCode spec t).eventTrace path.2.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (SourceNativeSampling.code t width).resourcePool path.1 +
    (recoveryCode spec t).resourcePool path.2.2 ≤ _
  rw [SourceNativeSampling.events]
  exact add_le_add le_rfl
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (model := Sampling.Native.Framed.model t width)
      (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width) (sampleInput t
        width)
      (resultRef t width) path.2.2)

/-- The complete path's sequential depth includes source sampling and recovery. -/
lemma code_depth_le {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat) (path : (code spec t).Path) :
    (code spec t).depth (fun _ => 1) path ≤ depthBudget t width := by
  change (SourceNativeSampling.code t width).depth (fun _ => 1) path.1 +
    (0 + (recoveryCode spec t).depth (fun _ => 1) path.2.2) ≤ _
  rw [Nat.zero_add, SourceNativeSampling.depth]
  exact Nat.add_le_add_left
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_unitDepth_le
      (model := Sampling.Native.Framed.model t width)
      (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width) (sampleInput t
        width)
      (resultRef t width) path.2.2) _

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
