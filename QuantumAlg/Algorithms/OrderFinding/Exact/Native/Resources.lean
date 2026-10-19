/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Execution
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.Space

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
public def eventBudget (t width : Nat) :
    ResourcePool (Sampling.Native.model t width) :=
  Sampling.Native.eventBudget t width +
    ClassicalRoutines.TerminalDecode.envelope
      (model := Sampling.Native.model t width) t

/-- Source depth followed by at most two unit events per decoded phase bit. -/
public def depthBudget (t width : Nat) : Nat :=
  Sampling.Native.depthBudget t width + 2 * t

/-- Every actual complete path fits the independent selected-model event pool. -/
lemma code_events_le (t width : Nat)
    (path : (code t width).Path) :
    (code t width).resourcePool path ≤ eventBudget t width := by
  change (Circuit.seq (sampleCode t width) (decoderCode t width)).Path at path
  change ResourcePool.ofList ((sampleCode t width).eventTrace path.1 ++
    (decoderCode t width).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  change (sampleCode t width).resourcePool path.1 +
    (decoderCode t width).resourcePool path.2 ≤ _
  have sampled :
      (sampleCode t width).resourcePool path.1 = Sampling.Native.eventBudget t width :=
    Sampling.Native.Framed.code_events Sampling.Native.pre samplePreNoQuantum t width path.1
  rw [sampled]
  exact add_le_add le_rfl
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model t width)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path.2)

/-- Sampling and decoding have their actual sequential unit-event depth. -/
lemma code_depth_le (t width : Nat)
    (path : (code t width).Path) :
    (code t width).depth (fun _ => 1) path ≤ depthBudget t width := by
  change (Circuit.seq (sampleCode t width) (decoderCode t width)).Path at path
  change (sampleCode t width).depth (fun _ => 1) path.1 +
    (decoderCode t width).depth (fun _ => 1) path.2 ≤ _
  have sampled :
      (sampleCode t width).depth (fun _ => 1) path.1 =
        Sampling.Native.depthBudget t width :=
    Sampling.Native.Framed.code_depth Sampling.Native.pre samplePreNoQuantum t width path.1
  rw [sampled]
  have decoded :=
    ClassicalRoutines.TerminalDecode.terminalDecode_routine_depth_le
      (model := Sampling.Native.model t width)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) (fun _ => 1) path.2
  change (decoderCode t width).depth (fun _ => 1) path.2 ≤ t * (1 + 1) at decoded
  unfold depthBudget
  omega

/-- Actual decoding adds no event outside its classical-operation coordinates. -/
private lemma decoder_count_nonclassical (t width : Nat) (path : (decoderCode t width).Path)
    (event : Resource.Event (Sampling.Native.model t width))
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event ((decoderCode t width).resourcePool path) = 0 := by
  have bound := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model t width) (samplePost t width) t .bigEndian
      (sampleInput t width) (resultKey t width) (resultFresh t width) path) event
  have zero : ResourcePool.count event
      (ClassicalRoutines.TerminalDecode.envelope (model := Sampling.Native.model t width) t) =
        0 := by
    simp [ClassicalRoutines.TerminalDecode.envelope, ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent, ClassicalRoutines.TerminalDecode.incrementEvent,
      nonclassical]
  rw [zero] at bound
  exact Nat.eq_zero_of_le_zero bound

/-- Every nonclassical coordinate is inherited exactly from the same source sample. -/
lemma code_count_nonclassical (t width : Nat) (path : (code t width).Path)
    (event : Resource.Event (Sampling.Native.model t width))
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event ((code t width).resourcePool path) =
      ResourcePool.count event (Sampling.Native.eventBudget t width) := by
  change ResourcePool.count event (ResourcePool.ofList
    ((sampleCode t width).eventTrace path.1 ++ (decoderCode t width).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count event ((sampleCode t width).resourcePool path.1) +
    ResourcePool.count event ((decoderCode t width).resourcePool path.2) = _
  rw [decoder_count_nonclassical t width path.2 event nonclassical, Nat.add_zero]
  have sampled : (sampleCode t width).resourcePool path.1 =
      Sampling.Native.eventBudget t width :=
    Sampling.Native.Framed.code_events Sampling.Native.pre samplePreNoQuantum t width path.1
  rw [sampled]

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
