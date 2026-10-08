/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Depth
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Depth
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Components.Classical.TerminalDecode.Resources

/-!
# Independent event and depth budgets for native exact order finding

The source sample charges its real preparation, native gates, one oracle
query, Z writes and packing. The retained decoder adds at most one shift and
one selected increment per phase bit on the same complete execution.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

/-- Independent coordinatewise allowance for sampling and real decoding. -/
def eventBudget {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    ResourcePool (Sampling.Native.model access) :=
  Sampling.Native.eventBudget access +
    ClassicalRoutines.TerminalDecode.envelope
      (model := Sampling.Native.model access) t

/-- Source depth followed by at most two unit events per decoded phase bit. -/
def depthBudget (t width : Nat) : Nat :=
  Sampling.Native.depthBudget t width + 2 * t

/-- Every actual complete path fits the independent selected-model event pool. -/
theorem code_events_le {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).resourcePool path ≤ eventBudget access := by
  change (Circuit.seq (sampleCode access) (decoderCode access)).Path at path
  change ResourcePool.ofList ((sampleCode access).eventTrace path.1 ++
    (decoderCode access).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (sampleCode access).resourcePool path.1 +
    (decoderCode access).resourcePool path.2 ≤ _
  have sampled :
      (sampleCode access).resourcePool path.1 = Sampling.Native.eventBudget access :=
    Sampling.Native.Framed.code_events Sampling.Native.pre samplePreNoQuantum access path.1
  rw [sampled]
  exact add_le_add le_rfl
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path.2)

/-- Sampling and decoding have their actual sequential unit-event depth. -/
theorem code_depth_le {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).depth (fun _ => 1) path ≤ depthBudget t width := by
  change (Circuit.seq (sampleCode access) (decoderCode access)).Path at path
  change (sampleCode access).depth (fun _ => 1) path.1 +
    (decoderCode access).depth (fun _ => 1) path.2 ≤ _
  have sampled :
      (sampleCode access).depth (fun _ => 1) path.1 =
        Sampling.Native.depthBudget t width :=
    Sampling.Native.Framed.code_depth Sampling.Native.pre samplePreNoQuantum access path.1
  rw [sampled]
  have decoded :=
    ClassicalRoutines.TerminalDecode.terminalDecode_routine_depth_le
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) (fun _ => 1) path.2
  change (decoderCode access).depth (fun _ => 1) path.2 ≤ t * (1 + 1) at decoded
  unfold depthBudget
  omega

/-- Actual decoding adds no event outside its classical-operation coordinates. -/
private theorem decoder_count_nonclassical {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (decoderCode access).Path)
    (event : Resource.Event (Sampling.Native.model access))
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event ((decoderCode access).resourcePool path) = 0 := by
  have bound := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model access) (samplePost t width) t .bigEndian
      (sampleInput t width) (resultKey t width) (resultFresh t width) path) event
  have zero : ResourcePool.count event
      (ClassicalRoutines.TerminalDecode.envelope (model := Sampling.Native.model access) t) =
        0 := by
    simp [ClassicalRoutines.TerminalDecode.envelope, ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent, ClassicalRoutines.TerminalDecode.incrementEvent,
      nonclassical]
  rw [zero] at bound
  exact Nat.eq_zero_of_le_zero bound

/-- Every nonclassical coordinate is inherited exactly from the same source sample. -/
theorem code_count_nonclassical {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path)
    (event : Resource.Event (Sampling.Native.model access))
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event ((code access).resourcePool path) =
      ResourcePool.count event (Sampling.Native.eventBudget access) := by
  change ResourcePool.count event (ResourcePool.ofList
    ((sampleCode access).eventTrace path.1 ++ (decoderCode access).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count event ((sampleCode access).resourcePool path.1) +
    ResourcePool.count event ((decoderCode access).resourcePool path.2) = _
  rw [decoder_count_nonclassical access path.2 event nonclassical, Nat.add_zero]
  have sampled : (sampleCode access).resourcePool path.1 =
      Sampling.Native.eventBudget access :=
    Sampling.Native.Framed.code_events Sampling.Native.pre samplePreNoQuantum access path.1
  rw [sampled]

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
