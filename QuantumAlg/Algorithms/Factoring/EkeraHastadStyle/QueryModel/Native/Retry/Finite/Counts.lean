/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Literal classical counts for the actual original-bank finite retry

Every real batch computes its sampled parameter, packs all sixteen working
measurements and additionally packs all sixteen persistent sample slots,
executes the complete native recovery, and performs optional selection.
The final pack is paid once. Preparation, reset measurements and corrections,
and the sealed original quantum member keep their own nonclassical labels.
The formula counts literal classical instructions, including whole-word
operations; it does not assert a bit-operation complexity bound.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- The independent pool observation includes both real packs per sample and each selector. -/
def classicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (Batch.sourceEventBudget N) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (LatticeFixedBatchRecoveryMachine.eventEnvelope (kind := .quantum) N) + 35) + 1

/-- The closed width ceiling includes the sixteen additional persistent sample packs per batch. -/
def scalarClassicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 198 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1

private theorem member_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight (memberEventBudget N) =
      1 := by
  simp [memberEventBudget, ShortDLP.preparationCircuit_eventCost,
    ShortDLP.readoutCircuit_eventCost, QFTCircuit_eventCost_eq, WalshHadamard.hadamardEvent,
    ShortDLP.oracleEvent, Circuit.zEvent, Resource.Event.classicalOperationWeight]

private theorem reset_classicalWeight (width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.Bank.envelope width) = 0 := by
  have one : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (ZReset.eventEnvelope 2) = 0 := rfl
  rw [ZReset.Bank.envelope, ResourcePool.weightedCount_nsmul, one, Nat.mul_zero]

private theorem selection_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Retry.selectionEventBudget N) = 3 := by
  simp [Retry.selectionEventBudget, Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, Resource.Event.classicalOperationWeight]

private theorem first_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Retry.firstEventBudget N) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Batch.sourceEventBudget N) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (LatticeFixedBatchRecoveryMachine.eventEnvelope (kind := .quantum) N) + 35 := by
  have prepared : Resource.Event.classicalOperationWeight (preparation N).event = 0 := rfl
  simp only [Retry.firstEventBudget, Batch.Recovery.firstEventBudget, Batch.firstEventBudget,
    Batch.setupEventBudget, Batch.reusedSampleEventBudget, reuseEventBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, prepared, member_classicalWeight,
    reset_classicalWeight, selection_classicalWeight, Batch.copyEvent]
  simp only [Resource.Event.classicalOperationWeight]
  omega

private theorem next_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Retry.nextEventBudget N) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Batch.sourceEventBudget N) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (LatticeFixedBatchRecoveryMachine.eventEnvelope (kind := .quantum) N) + 35 := by
  simp only [Retry.nextEventBudget, Batch.Recovery.nextEventBudget, Batch.nextEventBudget,
    Batch.reusedSampleEventBudget, reuseEventBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, member_classicalWeight,
    reset_classicalWeight, selection_classicalWeight, Batch.copyEvent,
    Resource.Event.classicalOperationWeight]
  omega

/-- The actual independent allowance has exactly the stated literal-classical observation. -/
theorem nativeOracle_finiteRetry_eventBudget_classicalWeight (N count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight (eventBudget N count) =
      classicalOperationBound N count := by
  cases count with
  | zero => rfl
  | succ count =>
      simp only [eventBudget, Retry.eventBudget, ResourcePool.scale,
        ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
        ResourcePool.weightedCount_singleton, first_classicalWeight, next_classicalWeight,
        Retry.packEvent, Resource.Event.classicalOperationWeight, classicalOperationBound]
      ring

private theorem sampler_classicalWeight_le (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Batch.sourceEventBudget N) ≤ 44 * modulusBits N + 163 := by
  have weighted := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event .quantum => 1)
    (s := ShorStyle.Canonical.Sampler.Retained.nativeEnvelope .quantum N)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [Batch.sourceEventBudget, ResourcePool.weightedCount, Multiset.map_const',
    Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one,
    ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card, modulusBits] using weighted

/-- The literal-classical pool formula is bounded by the complete independent width ceiling. -/
theorem nativeOracle_finiteRetry_classicalOperationBound_le_scalar (N count : Nat) :
    classicalOperationBound N count ≤ scalarClassicalOperationBound N count := by
  cases count with
  | zero => exact le_rfl
  | succ count =>
      have sampler := sampler_classicalWeight_le N
      have recovery := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
        (kind := .quantum) N
      unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width at recovery
      have batch : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
            (Batch.sourceEventBudget N) +
          ResourcePool.weightedCount Resource.Event.classicalOperationWeight
            (LatticeFixedBatchRecoveryMachine.eventEnvelope (kind := .quantum) N) + 35 ≤
          44 * modulusBits N + 198 + LatticeFixedBatchRecoveryMachine.eventCountBound
            (modulusBits N) (shortLogBits N) (tradeoffBits N)
            (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left (count + 1) batch) 1

-- Keep the actual dependent run abstract while using its already established pool bound.
attribute [local irreducible] run code context

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Literal classical operations on each path of this same actual run obey the width ceiling. -/
theorem nativeOracle_finiteRetry_classicalOperation_le_widthBound (input : Input N) (count : Nat)
    (path : (run base noQuantum N input count).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum N input count).code.resourcePool path) ≤
        scalarClassicalOperationBound N count := by
  have pools := nativeOracle_finiteRetry_resourcePool_le base noQuantum N input count
  rw [← nativeOracle_finiteRetry_run_code base noQuantum N input count] at pools
  exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight (pools path)).trans
    ((nativeOracle_finiteRetry_eventBudget_classicalWeight N count).trans_le
      (nativeOracle_finiteRetry_classicalOperationBound_le_scalar N count))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Retry.Finite
