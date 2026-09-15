/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Recovery
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Space

/-!
# Actual original-bank sampling followed by complete native recovery

The existing recovery consumes the actual fixed sixteen sample slots and
stored parameter. Its complete native allowance follows the real sampling
allowance. Arbitrary durations retain the sampling tensor critical paths;
only the classical recovery uses its weighted native pool. Source, reset and
recovery scopes are sequential, so their additional live space is a maximum
beside the one fixed bank and all retained results.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery

open Execution

noncomputable section

/-- Every actual first-batch event is followed by the complete original recovery allowance. -/
def firstEventBudget (N : Nat) : ResourcePool .quantum :=
  Batch.firstEventBudget N + LatticeFixedBatchRecoveryMachine.eventEnvelope N

/-- Every actual later-batch event is followed by the same complete original recovery. -/
def nextEventBudget (N : Nat) : ResourcePool .quantum :=
  Batch.nextEventBudget N + LatticeFixedBatchRecoveryMachine.eventEnvelope N

/-- The actual first sampling critical path precedes the weighted classical recovery budget. -/
def firstDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  Batch.firstDurationBudget N duration + ResourcePool.weightedCount duration
    (LatticeFixedBatchRecoveryMachine.eventEnvelope N)

/-- The actual later sampling critical path precedes the same classical recovery budget. -/
def nextDurationBudget (N : Nat) (duration : Resource.Event .quantum → Nat) : Nat :=
  Batch.nextDurationBudget N duration + ResourcePool.weightedCount duration
    (LatticeFixedBatchRecoveryMachine.eventEnvelope N)

/-- The actual source/reset scopes and complete recovery work never coexist. -/
def scratchSpace (N : Nat) : SpacePool .quantum :=
  SpacePool.max (Batch.scratchSpace N) (LatticeFixedBatchRecoveryMachine.additionalSpace N)

/-- Fixed results and the sole bank remain live beside the largest real temporary allowance. -/
def additionalSpace (N : Nat) : SpacePool .quantum := Batch.retainedSpace N + scratchSpace N

private theorem sampler_allowance (N : Nat) (caller : SpacePool .quantum) :
    Batch.additionalSpace N + caller ≤ additionalSpace N + caller :=
  add_le_add (add_le_add (le_refl _) (SpacePool.le_max_left _ _)) (le_refl _)

private theorem recovery_allowance (N : Nat) (caller : SpacePool .quantum) :
    LatticeFixedBatchRecoveryMachine.additionalSpace N + (Batch.retainedSpace N + caller) ≤
      additionalSpace N + caller := by
  intro axis
  have bounded := SpacePool.le_max_right (Batch.scratchSpace N)
    (LatticeFixedBatchRecoveryMachine.additionalSpace N) axis
  change _ ≤ scratchSpace N axis at bounded
  change LatticeFixedBatchRecoveryMachine.additionalSpace N axis +
    (Batch.retainedSpace N axis + caller axis) ≤
      (Batch.retainedSpace N axis + scratchSpace N axis) + caller axis
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem recovery_pool (input : Input N) (path : (into base noQuantum N input).Path) :
    (into base noQuantum N input).resourcePool path ≤
      LatticeFixedBatchRecoveryMachine.eventEnvelope N :=
  LatticeFixedBatchRecoveryMachine.into_pool_le input (parameter base noQuantum N)
    (terminals base noQuantum N) (Batch.factorRef base noQuantum N) path

/-- The actual first sampler and recovery meet their separate native allowances on one path. -/
theorem nativeOracle_recovery_first_resourcePool_le (input : Input N)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).resourcePool path ≤ firstEventBudget N := by
  change (Batch.code base noQuantum N input).resourcePool path.1 +
    (into base noQuantum N input).resourcePool path.2 ≤ _
  exact add_le_add (Batch.nativeOracle_batch_resourcePool_le base noQuantum N input path.1)
    (recovery_pool base noQuantum N input path.2)

/-- Arbitrary durations retain the actual first sampling dependencies before classical recovery. -/
theorem nativeOracle_recovery_first_depth_le (input : Input N)
    (duration : Resource.Event .quantum → Nat) (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).depth duration path ≤ firstDurationBudget N duration := by
  change (Batch.code base noQuantum N input).depth duration path.1 +
    (into base noQuantum N input).depth duration path.2 ≤ _
  exact Nat.add_le_add (Batch.nativeOracle_batch_depth_le base noQuantum N input duration path.1)
    (Circuit.depth_le_weightedCount_of_pool_le (into base noQuantum N input) duration
      (LatticeFixedBatchRecoveryMachine.eventEnvelope N) path.2
      (recovery_pool base noQuantum N input path.2))

/-- Actual first sampling and recovery share a resident scratch maximum beside fixed storage. -/
theorem nativeOracle_recovery_first_peakResidentSpace_le (input : Input N)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have sampled := (Batch.nativeOracle_batch_peakResidentSpace_le
    base noQuantum N input path.1).trans
    (sampler_allowance N base.residentSpace)
  have recovered := LatticeFixedBatchRecoveryMachine.into_resident_le input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) path.2
  have aligned := congrArg
    (fun space => LatticeFixedBatchRecoveryMachine.additionalSpace N + space)
    (Batch.nativeOracle_batch_context_residentSpace base noQuantum N)
  exact (Circuit.peakResidentSpace_seq (Batch.code base noQuantum N input)
    (into base noQuantum N input) path).le.trans
      (SpacePool.max_le sampled
        (recovered.trans (aligned.trans_le (recovery_allowance N base.residentSpace))))

/-- Actual first sampling and recovery share a auxiliary scratch maximum beside fixed storage. -/
theorem nativeOracle_recovery_first_peakAuxiliarySpace_le (input : Input N)
    (path : (first base noQuantum N input).Path) :
    (first base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have sampled := (Batch.nativeOracle_batch_peakAuxiliarySpace_le
    base noQuantum N input path.1).trans
    (sampler_allowance N base.auxiliarySpace)
  have recovered := LatticeFixedBatchRecoveryMachine.into_auxiliary_le input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) path.2
  have aligned := congrArg
    (fun space => LatticeFixedBatchRecoveryMachine.additionalSpace N + space)
    (Batch.nativeOracle_batch_context_auxiliarySpace base noQuantum N)
  exact (Circuit.peakAuxiliarySpace_seq (Batch.code base noQuantum N input)
    (into base noQuantum N input) path).le.trans
      (SpacePool.max_le sampled
        (recovered.trans (aligned.trans_le (recovery_allowance N base.auxiliarySpace))))

/-- The actual next sampler and recovery meet their separate native allowances on one path. -/
theorem nativeOracle_recovery_next_resourcePool_le (input : Input N)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).resourcePool path ≤ nextEventBudget N := by
  change (Batch.nextBatch base noQuantum N input).resourcePool path.1 +
    (into base noQuantum N input).resourcePool path.2 ≤ _
  exact add_le_add (Batch.nativeOracle_nextBatch_resourcePool_le base noQuantum N input path.1)
    (recovery_pool base noQuantum N input path.2)

/-- Arbitrary durations retain the actual next sampling dependencies before classical recovery. -/
theorem nativeOracle_recovery_next_depth_le (input : Input N)
    (duration : Resource.Event .quantum → Nat) (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).depth duration path ≤ nextDurationBudget N duration := by
  change (Batch.nextBatch base noQuantum N input).depth duration path.1 +
    (into base noQuantum N input).depth duration path.2 ≤ _
  exact Nat.add_le_add
    (Batch.nativeOracle_nextBatch_depth_le base noQuantum N input duration path.1)
    (Circuit.depth_le_weightedCount_of_pool_le (into base noQuantum N input) duration
      (LatticeFixedBatchRecoveryMachine.eventEnvelope N) path.2
      (recovery_pool base noQuantum N input path.2))

/-- Actual next sampling and recovery share a resident scratch maximum beside fixed storage. -/
theorem nativeOracle_recovery_next_peakResidentSpace_le (input : Input N)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakResidentSpace path ≤
      additionalSpace N + base.residentSpace := by
  have sampled := (Batch.nativeOracle_nextBatch_peakResidentSpace_le
    base noQuantum N input path.1).trans
    (sampler_allowance N base.residentSpace)
  have recovered := LatticeFixedBatchRecoveryMachine.into_resident_le input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) path.2
  have aligned := congrArg
    (fun space => LatticeFixedBatchRecoveryMachine.additionalSpace N + space)
    (Batch.nativeOracle_batch_context_residentSpace base noQuantum N)
  exact (Circuit.peakResidentSpace_seq (Batch.nextBatch base noQuantum N input)
    (into base noQuantum N input) path).le.trans
      (SpacePool.max_le sampled
        (recovered.trans (aligned.trans_le (recovery_allowance N base.residentSpace))))

/-- Actual next sampling and recovery share a auxiliary scratch maximum beside fixed storage. -/
theorem nativeOracle_recovery_next_peakAuxiliarySpace_le (input : Input N)
    (path : (next base noQuantum N input).Path) :
    (next base noQuantum N input).peakAuxiliarySpace path ≤
      additionalSpace N + base.auxiliarySpace := by
  have sampled := (Batch.nativeOracle_nextBatch_peakAuxiliarySpace_le
    base noQuantum N input path.1).trans
    (sampler_allowance N base.auxiliarySpace)
  have recovered := LatticeFixedBatchRecoveryMachine.into_auxiliary_le input
    (parameter base noQuantum N) (terminals base noQuantum N)
    (Batch.factorRef base noQuantum N) path.2
  have aligned := congrArg
    (fun space => LatticeFixedBatchRecoveryMachine.additionalSpace N + space)
    (Batch.nativeOracle_batch_context_auxiliarySpace base noQuantum N)
  exact (Circuit.peakAuxiliarySpace_seq (Batch.nextBatch base noQuantum N input)
    (into base noQuantum N input) path).le.trans
      (SpacePool.max_le sampled
        (recovered.trans (aligned.trans_le (recovery_allowance N base.auxiliarySpace))))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Recovery
