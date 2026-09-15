/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.EventKinds
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Primitives.WalshHadamard

/-!
# Exact original quantum counts of the complete native general run

All continued-fraction recovery and modular validation events are actual
classical operations. The full execution therefore retains the original
source gate, query, preparation and Z-measurement coordinates exactly.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

/-- Actual native recovery leaves every non-classical source coordinate unchanged. -/
theorem code_nonclassicalCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (code hinput A).Path) (event : Resource.Event .quantum)
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event ((code hinput A).resourcePool path) =
      ResourcePool.count event (Sampling.eventBudget N x t width) := by
  change ResourcePool.count event (ResourcePool.ofList
    ((NativeSampling.code A).eventTrace path.1 ++
      (recoveryCode hinput A).eventTrace path.2.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count event ((NativeSampling.code A).resourcePool path.1) +
    ResourcePool.count event ((recoveryCode hinput A).resourcePool path.2.2) = _
  have sampled := congrArg (ResourcePool.count event) (NativeSampling.events A path.1)
  have recovered :
      ResourcePool.count event ((recoveryCode hinput A).resourcePool path.2.2) = 0 :=
    ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_count_nonclassical
      (recoverySpec hinput A) (baseInput t width) (sampleInput t width)
      (resultRef t width) path.2.2 event nonclassical
  exact (congrArg₂ Nat.add sampled recovered).trans (Nat.add_zero _)

/-- Each actual complete run makes one original modular-exponentiation query. -/
theorem code_modExpCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (code hinput A).Path) :
    ResourcePool.count (modExpEvent N x t width) ((code hinput A).resourcePool path) = 1 := by
  rw [code_nonclassicalCount hinput A path _ (by intro operation; simp [modExpEvent])]
  simp [Sampling.eventBudget, Sampling.unitaryEventBudget, Sampling.basisPreparationEvent,
    modExpEvent, WalshHadamard.hadamardEvent]

/-- Full recovery preserves each literal quantum-gate coordinate of the source sample. -/
theorem code_gateCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (code hinput A).Path) (label : Resource.GateLabel) :
    ResourcePool.count (.gate label) ((code hinput A).resourcePool path) =
      ResourcePool.count (.gate label) (Sampling.unitaryEventBudget N x t width) := by
  rw [code_nonclassicalCount hinput A path _ (by intro operation; simp)]
  simp [Sampling.eventBudget, Sampling.basisPreparationEvent]

/-- Every actual full path has the original exact Hadamard, controlled-phase and SWAP counts. -/
theorem code_quantumGateCounts {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (path : (code hinput A).Path) :
    ResourcePool.count (.gate (.builtin "hadamard")) ((code hinput A).resourcePool path) =
        2 * t ∧
      ResourcePool.count (.gate qftControlledPhaseLabel) ((code hinput A).resourcePool path) =
        t * (t - 1) / 2 ∧
      ResourcePool.count (.gate (.builtin "swap")) ((code hinput A).resourcePool path) =
        t / 2 := by
  simp [code_gateCount, Sampling.unitaryEventBudget, modExpEvent,
    WalshHadamard.hadamardEvent, qftControlledPhaseLabel, Nat.choose_two_right,
    two_mul, Resource.GateLabel.controlForDimension, Resource.GateLabel.builtin,
    Resource.GateLabel.controlForDimensions, Resource.GateLabel.declared]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
