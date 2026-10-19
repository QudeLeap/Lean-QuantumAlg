/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Resources
public import QuantumAlg.Core.Base.Accounting.Event
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Resources

/-!
# Physical reset bounds and independent cleanup allowances

Each reset pays one Z and at most one X per original bank wire, with one
scoped classical scratch bit per wire and no extra quantum system. The scalar
allowances combine a finite retry allowance with one terminal reset.
Canonical completed execution instead composes the retained primitive
bounds for every paid pack and physical reset.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable {N : Nat}

/-- Every positive execution pays the raw event allowance and the actual final reset envelope. -/
def eventBudget (N : Nat) : Nat → ResourcePool (model N)
  | 0 => 0
  | laterCount + 1 => Finite.eventBudget N (laterCount + 1) + resetEventBudget N

/-- A further independently completed batch pays its recovery/selection,
an explicit selected-result pack, and an additional terminal physical reset. -/
def nextCompletedEventBudget (N : Nat) : ResourcePool (model N) :=
  (Retry.nextEventBudget N + ResourcePool.singleton (Retry.packEvent N)) +
    resetEventBudget N

/-- The two completed physical batches pay the first complete run and one
further complete segment independently, including two real resets. -/
def twoCompletedEventBudget (N : Nat) : ResourcePool (model N) :=
  eventBudget N 1 + nextCompletedEventBudget N

/-- The final measurement/correction path follows every real retry and the packed result. -/
public def durationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat → Nat
  | 0 => 0
  | laterCount + 1 => Finite.durationBudget N duration (laterCount + 1) +
      resetDurationBudget N duration

/-- Serial allowance for the same further batch, including the newly paid
pack and terminal measurement/correction dependency. -/
def nextCompletedDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  (Retry.nextDurationBudget N duration + duration (Retry.packEvent N)) +
    resetDurationBudget N duration

/-- Whole-run serial duration for the real two-batch circuit. -/
def twoCompletedDurationBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  durationBudget N duration 1 + nextCompletedDurationBudget N duration

/-- Maximum of the two independently completed batch allowances, distinct
from their serial whole-run duration. -/
public def twoCompletedMaximumBatchBudget (N : Nat)
    (duration : Resource.Event (model N) → Nat) : Nat :=
  max (durationBudget N duration 1) (nextCompletedDurationBudget N duration)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

lemma reset_pool (path : (reset base noQuantum N).Path) :
    (reset base noQuantum N).resourcePool path ≤ resetEventBudget N :=
  declaredReuse_reset_resourcePool_le (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N path

lemma reset_depth (duration : Resource.Event (model N) → Nat)
    (path : (reset base noQuantum N).Path) :
    (reset base noQuantum N).depth duration path ≤ resetDurationBudget N duration :=
  declaredReuse_reset_depth_le (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N duration path

private lemma scratch_le (N : Nat) :
    resetSpace N ≤ Batch.Recovery.scratchSpace N :=
  (SpacePool.le_max_right
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (resetSpace N)).trans
      (SpacePool.le_max_left (Batch.scratchSpace N) (Batch.Recovery.recoverySpace N))

lemma reset_resident (path : (reset base noQuantum N).Path) :
    (reset base noQuantum N).peakResidentSpace path ≤
      Retry.additionalSpace N + base.residentSpace := by
  have peak := declaredReuse_reset_peakResidentSpace
    (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N path
  refine peak.le.trans ?_
  change resetSpace N + (Retry.context base noQuantum N).residentSpace ≤ _
  rw [Retry.declaredRetry_context_residentSpace]
  intro axis
  have scratch : resetSpace N axis ≤ Batch.Recovery.scratchSpace N axis :=
    scratch_le N axis
  change resetSpace N axis +
    ((Batch.retainedSpace N axis + Retry.selectorSpace N axis) + base.residentSpace axis) ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.residentSpace axis
  omega

lemma reset_auxiliary (path : (reset base noQuantum N).Path) :
    (reset base noQuantum N).peakAuxiliarySpace path ≤
      Retry.additionalSpace N + base.auxiliarySpace := by
  have peak := declaredReuse_reset_peakAuxiliarySpace
    (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N path
  refine peak.le.trans ?_
  change resetSpace N + (Retry.context base noQuantum N).auxiliarySpace ≤ _
  rw [Retry.declaredRetry_context_auxiliarySpace]
  intro axis
  have scratch : resetSpace N axis ≤ Batch.Recovery.scratchSpace N axis :=
    scratch_le N axis
  change resetSpace N axis +
    ((Batch.retainedSpace N axis + Retry.selectorSpace N axis) + base.auxiliarySpace axis) ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.auxiliarySpace axis
  omega

-- Keep the already-certified finite body and reset opaque during the scoped
-- sequence accounting; only their outer composition is needed here.
attribute [local irreducible] reset

private lemma seq_pool_le {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    (leftBudget rightBudget : ResourcePool model)
    (leftBound : ∀ path, first.resourcePool path ≤ leftBudget)
    (rightBound : ∀ path, second.resourcePool path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).resourcePool path ≤ leftBudget + rightBudget := by
  rcases path with ⟨leftPath, rightPath⟩
  change first.resourcePool leftPath + second.resourcePool rightPath ≤ _
  exact add_le_add (leftBound leftPath) (rightBound rightPath)

private lemma seq_depth_le {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle) (second : Circuit model middle post)
    (duration : Resource.Event model → Nat)
    (leftBudget rightBudget : Nat)
    (leftBound : ∀ path, first.depth duration path ≤ leftBudget)
    (rightBound : ∀ path, second.depth duration path ≤ rightBudget)
    (path : (first.seq second).Path) :
    (first.seq second).depth duration path ≤ leftBudget + rightBudget := by
  rcases path with ⟨leftPath, rightPath⟩
  change first.depth duration leftPath + second.depth duration rightPath ≤ _
  exact Nat.add_le_add (leftBound leftPath) (rightBound rightPath)

private lemma pack_pool (path : (Retry.pack base noQuantum N).Path) :
    (Retry.pack base noQuantum N).resourcePool path ≤
      ResourcePool.singleton (Retry.packEvent N) := by
  change ResourcePool.singleton (Retry.packEvent N) ≤
    ResourcePool.singleton (Retry.packEvent N)
  exact le_refl _

private lemma pack_depth (duration : Resource.Event (model N) → Nat)
    (path : (Retry.pack base noQuantum N).Path) :
    (Retry.pack base noQuantum N).depth duration path ≤
      duration (Retry.packEvent N) := by
  change duration (Retry.packEvent N) ≤ duration (Retry.packEvent N)
  exact le_refl _

private lemma nextPack_pool
    (path : ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N)).Path) :
    ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N)).resourcePool path ≤
      Retry.nextEventBudget N + ResourcePool.singleton (Retry.packEvent N) :=
  seq_pool_le (Retry.next base noQuantum N input) (Retry.pack base noQuantum N)
    (Retry.nextEventBudget N) (ResourcePool.singleton (Retry.packEvent N))
    (Retry.next_pool base noQuantum N input) (pack_pool base noQuantum N) path

private lemma nextPack_depth (duration : Resource.Event (model N) → Nat)
    (path : ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N)).Path) :
    ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N)).depth duration path ≤
      Retry.nextDurationBudget N duration + duration (Retry.packEvent N) :=
  seq_depth_le (Retry.next base noQuantum N input) (Retry.pack base noQuantum N)
    duration (Retry.nextDurationBudget N duration) (duration (Retry.packEvent N))
    (Retry.next_depth base noQuantum N input duration)
    (pack_depth base noQuantum N duration) path

/-- The further completed segment's actual path fits its independently
stated event allowance, with both the extra pack and reset charged. -/
lemma nextCompleted_resourcePool_le
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).resourcePool path ≤
      nextCompletedEventBudget N := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N)).seq
      (reset base noQuantum N)).resourcePool path ≤
    (Retry.nextEventBudget N + ResourcePool.singleton (Retry.packEvent N)) +
      resetEventBudget N
  exact seq_pool_le
    ((Retry.next base noQuantum N input).seq (Retry.pack base noQuantum N))
    (reset base noQuantum N)
    (Retry.nextEventBudget N + ResourcePool.singleton (Retry.packEvent N))
    (resetEventBudget N)
    (nextPack_pool base noQuantum N input)
    (reset_pool base noQuantum N) path

/-- The further batch retains all actual sequential dependencies through
selection, the extra pack, and physical cleanup. -/
lemma nextCompleted_depth_le (duration : Resource.Event (model N) → Nat)
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).depth duration path ≤
      nextCompletedDurationBudget N duration := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N)).seq
      (reset base noQuantum N)).depth duration path ≤
    (Retry.nextDurationBudget N duration + duration (Retry.packEvent N)) +
      resetDurationBudget N duration
  exact seq_depth_le
    ((Retry.next base noQuantum N input).seq (Retry.pack base noQuantum N))
    (reset base noQuantum N) duration
    (Retry.nextDurationBudget N duration + duration (Retry.packEvent N))
    (resetDurationBudget N duration)
    (nextPack_depth base noQuantum N input duration)
    (reset_depth base noQuantum N duration) path

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
