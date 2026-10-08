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
scoped classical scratch bit and no extra quantum system. The scalar
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
def eventBudget (input : Input N) : Nat → ResourcePool (model input)
  | 0 => 0
  | laterCount + 1 => Finite.eventBudget input (laterCount + 1) + resetEventBudget input

/-- A further independently completed batch pays its recovery/selection,
an explicit selected-result pack, and an additional terminal physical reset. -/
def nextCompletedEventBudget (input : Input N) : ResourcePool (model input) :=
  (Retry.nextEventBudget input + ResourcePool.singleton (Retry.packEvent input)) +
    resetEventBudget input

/-- The two completed physical batches pay the first complete run and one
further complete segment independently, including two real resets. -/
def twoCompletedEventBudget (input : Input N) : ResourcePool (model input) :=
  eventBudget input 1 + nextCompletedEventBudget input

/-- The final measurement/correction path follows every real retry and the packed result. -/
public def durationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat → Nat
  | 0 => 0
  | laterCount + 1 => Finite.durationBudget input duration (laterCount + 1) +
      resetDurationBudget input duration

/-- Serial allowance for the same further batch, including the newly paid
pack and terminal measurement/correction dependency. -/
def nextCompletedDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  (Retry.nextDurationBudget input duration + duration (Retry.packEvent input)) +
    resetDurationBudget input duration

/-- Whole-run serial duration for the real two-batch circuit. -/
def twoCompletedDurationBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  durationBudget input duration 1 + nextCompletedDurationBudget input duration

/-- Maximum of the two independently completed batch allowances, distinct
from their serial whole-run duration. -/
public def twoCompletedMaximumBatchBudget (input : Input N)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  max (durationBudget input duration 1) (nextCompletedDurationBudget input duration)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

theorem reset_pool (path : (reset base noQuantum N input).Path) :
    (reset base noQuantum N input).resourcePool path ≤ resetEventBudget input :=
  declaredReuse_reset_resourcePool_le (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N input path

theorem reset_depth (duration : Resource.Event (model input) → Nat)
    (path : (reset base noQuantum N input).Path) :
    (reset base noQuantum N input).depth duration path ≤ resetDurationBudget input duration :=
  declaredReuse_reset_depth_le (Batch.storageContext (Retry.callerContext base N) N)
    (Batch.storage_empty (Retry.callerContext base N) (Retry.caller_empty base noQuantum N) N)
    N input duration path

private theorem scratch_le (N : Nat) :
    SpacePool.ofShape (.finite 2) ≤ Batch.Recovery.scratchSpace N :=
  (SpacePool.le_max_right
    (ShorStyle.Canonical.Sampler.Program.additionalSpace .quantum (modulusBits N))
    (SpacePool.ofShape (.finite 2))).trans
      (SpacePool.le_max_left (Batch.scratchSpace N) (Batch.Recovery.recoverySpace N))

theorem reset_resident (path : (reset base noQuantum N input).Path) :
    (reset base noQuantum N input).peakResidentSpace path ≤
      Retry.additionalSpace N + base.residentSpace := by
  have peak := ZReset.BankScope.zResetBankScope_peakResidentSpace
    (oracles := ShortDLP.declaredModel (Native.encoding input)) (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Retry.context_wires base noQuantum N)) path
  refine peak.le.trans ?_
  rw [Retry.declaredRetry_context_residentSpace]
  intro axis
  have scratch : SpacePool.ofShape (.finite 2) axis ≤
      Batch.Recovery.scratchSpace N axis := scratch_le N axis
  change SpacePool.ofShape (.finite 2) axis +
    ((Batch.retainedSpace N axis + Retry.selectorSpace N axis) + base.residentSpace axis) ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.residentSpace axis
  exact (Nat.add_le_add_right scratch _).trans (by omega)

theorem reset_auxiliary (path : (reset base noQuantum N input).Path) :
    (reset base noQuantum N input).peakAuxiliarySpace path ≤
      Retry.additionalSpace N + base.auxiliarySpace := by
  have peak := ZReset.BankScope.zResetBankScope_peakAuxiliarySpace
    (oracles := ShortDLP.declaredModel (Native.encoding input)) (operations := BitWord.model)
    (Native.nativeOracle_context_qubits N (Retry.context_wires base noQuantum N)) path
  refine peak.le.trans ?_
  rw [Retry.declaredRetry_context_auxiliarySpace]
  intro axis
  have scratch : SpacePool.ofShape (.finite 2) axis ≤
      Batch.Recovery.scratchSpace N axis := scratch_le N axis
  change SpacePool.ofShape (.finite 2) axis +
    ((Batch.retainedSpace N axis + Retry.selectorSpace N axis) + base.auxiliarySpace axis) ≤
      ((Batch.retainedSpace N axis + Batch.Recovery.scratchSpace N axis) +
        Retry.selectorSpace N axis) + base.auxiliarySpace axis
  exact (Nat.add_le_add_right scratch _).trans (by omega)

-- Keep the already-certified finite body and reset opaque during the scoped
-- sequence accounting; only their outer composition is needed here.
attribute [local irreducible] reset

private theorem seq_pool_le {model : ExecutionModel}
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

private theorem seq_depth_le {model : ExecutionModel}
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

private theorem pack_pool (path : (Retry.pack base noQuantum N input).Path) :
    (Retry.pack base noQuantum N input).resourcePool path ≤
      ResourcePool.singleton (Retry.packEvent input) := by
  change ResourcePool.singleton (Retry.packEvent input) ≤
    ResourcePool.singleton (Retry.packEvent input)
  exact le_refl _

private theorem pack_depth (duration : Resource.Event (model input) → Nat)
    (path : (Retry.pack base noQuantum N input).Path) :
    (Retry.pack base noQuantum N input).depth duration path ≤
      duration (Retry.packEvent input) := by
  change duration (Retry.packEvent input) ≤ duration (Retry.packEvent input)
  exact le_refl _

private theorem nextPack_pool
    (path : ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N input)).Path) :
    ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N input)).resourcePool path ≤
      Retry.nextEventBudget input + ResourcePool.singleton (Retry.packEvent input) :=
  seq_pool_le (Retry.next base noQuantum N input) (Retry.pack base noQuantum N input)
    (Retry.nextEventBudget input) (ResourcePool.singleton (Retry.packEvent input))
    (Retry.next_pool base noQuantum N input) (pack_pool base noQuantum N input) path

private theorem nextPack_depth (duration : Resource.Event (model input) → Nat)
    (path : ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N input)).Path) :
    ((Retry.next base noQuantum N input).seq
      (Retry.pack base noQuantum N input)).depth duration path ≤
      Retry.nextDurationBudget input duration + duration (Retry.packEvent input) :=
  seq_depth_le (Retry.next base noQuantum N input) (Retry.pack base noQuantum N input)
    duration (Retry.nextDurationBudget input duration) (duration (Retry.packEvent input))
    (Retry.next_depth base noQuantum N input duration)
    (pack_depth base noQuantum N input duration) path

/-- The further completed segment's actual path fits its independently
stated event allowance, with both the extra pack and reset charged. -/
theorem nextCompleted_resourcePool_le
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).resourcePool path ≤
      nextCompletedEventBudget input := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N input)).seq
      (reset base noQuantum N input)).resourcePool path ≤
    (Retry.nextEventBudget input + ResourcePool.singleton (Retry.packEvent input)) +
      resetEventBudget input
  exact seq_pool_le
    ((Retry.next base noQuantum N input).seq (Retry.pack base noQuantum N input))
    (reset base noQuantum N input)
    (Retry.nextEventBudget input + ResourcePool.singleton (Retry.packEvent input))
    (resetEventBudget input)
    (nextPack_pool base noQuantum N input)
    (reset_pool base noQuantum N input) path

/-- The further batch retains all actual sequential dependencies through
selection, the extra pack, and physical cleanup. -/
theorem nextCompleted_depth_le (duration : Resource.Event (model input) → Nat)
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCode base noQuantum N input).depth duration path ≤
      nextCompletedDurationBudget input duration := by
  change (((Retry.next base noQuantum N input).seq
    (Retry.pack base noQuantum N input)).seq
      (reset base noQuantum N input)).depth duration path ≤
    (Retry.nextDurationBudget input duration + duration (Retry.packEvent input)) +
      resetDurationBudget input duration
  exact seq_depth_le
    ((Retry.next base noQuantum N input).seq (Retry.pack base noQuantum N input))
    (reset base noQuantum N input) duration
    (Retry.nextDurationBudget input duration + duration (Retry.packEvent input))
    (resetDurationBudget input duration)
    (nextPack_depth base noQuantum N input duration)
    (reset_depth base noQuantum N input duration) path

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
