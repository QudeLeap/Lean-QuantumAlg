/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Resources.Sample
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Recovery.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Counts
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Pure classical counts for declared EH batch allowances

Each batch computes its sampled parameter, packs sixteen working results
and sixteen persistent samples, and performs recovery and optional selection.
The scalar formulas in this owner use one final result pack. Completed
execution bounds separately account for the additional per-batch packs.
These counts measure literal whole-word classical instructions, not bit
operations; preparation and physical reset retain nonclassical labels.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

/-- The independent pool observation includes both real packs per sample and each selector. -/
def classicalOperationBound {N : Nat} (input : Input N) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (Batch.sourceEventBudget input) +
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model input) N) + 35) + 1

/-- The closed width ceiling includes the sixteen additional persistent sample packs per batch. -/
def scalarClassicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 198 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))) + 1

private theorem word_classicalWeight {gates : GateModel} {oracles : OracleModel}
    {width : Nat} {layout : QuantumLayout width}
    (word : UnitaryCircuit gates oracles layout)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (word.eventCost operations services) = 0 := by
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event emitted
  cases event with
  | classicalOperation coordinate =>
      have absent := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        word operations services (.classicalOperation coordinate)
      have positive := Multiset.count_pos.mpr emitted
      change 0 < ResourcePool.count (.classicalOperation coordinate)
        (word.eventCost operations services) at positive
      rw [absent] at positive
      exact False.elim (Nat.not_lt_zero _ positive)
  | _ => rfl

private theorem member_classicalWeight {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight (memberEventBudget input) =
      1 := by
  simp [memberEventBudget, word_classicalWeight, Resource.Event.classicalOperationWeight]

private theorem reset_classicalWeight {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (resetEventBudget input) = 0 := by
  simp [resetEventBudget, ZReset.Bank.envelope, ZReset.eventEnvelope,
    Resource.Event.classicalOperationWeight]

private theorem selection_classicalWeight {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Retry.selectionEventBudget input) = 3 := by
  simp [Retry.selectionEventBudget, Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, Resource.Event.classicalOperationWeight]

private theorem first_classicalWeight {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Retry.firstEventBudget input) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Batch.sourceEventBudget input) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model input) N) + 35 := by
  simp only [Retry.firstEventBudget, Batch.Recovery.firstEventBudget, Batch.firstEventBudget,
    Batch.setupEventBudget, Batch.reusedSampleEventBudget, reuseEventBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, preparationEventBudget, member_classicalWeight,
    reset_classicalWeight, selection_classicalWeight, Batch.copyEvent]
  simp only [Resource.Event.classicalOperationWeight]
  omega

private theorem next_classicalWeight {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Retry.nextEventBudget input) =
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Batch.sourceEventBudget input) +
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model input) N) + 35 := by
  simp only [Retry.nextEventBudget, Batch.Recovery.nextEventBudget, Batch.nextEventBudget,
    Batch.reusedSampleEventBudget, reuseEventBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, member_classicalWeight,
    reset_classicalWeight, selection_classicalWeight, Batch.copyEvent,
    Resource.Event.classicalOperationWeight]
  omega

/-- The actual independent allowance has exactly the stated literal-classical observation. -/
theorem declaredCleanup_eventBudget_classicalWeight {N : Nat} (input : Input N) (count : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight (eventBudget input count) =
      classicalOperationBound input count := by
  cases count with
  | zero => rfl
  | succ count =>
      simp only [eventBudget, Finite.eventBudget, Retry.eventBudget, ResourcePool.scale,
        ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
        ResourcePool.weightedCount_singleton, first_classicalWeight, next_classicalWeight,
        reset_classicalWeight, Retry.packEvent, Resource.Event.classicalOperationWeight,
        classicalOperationBound]
      ring

private theorem sampler_classicalWeight_le {N : Nat} (input : Input N) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Batch.sourceEventBudget input) ≤ 44 * modulusBits N + 163 := by
  have weighted := Multiset.sum_map_le_sum_map Resource.Event.classicalOperationWeight
    (fun _ : Resource.Event (model input) => 1)
    (s := ShorStyle.Canonical.Sampler.Retained.nativeEnvelope (model input) N)
    (fun event _ => by cases event <;> simp [Resource.Event.classicalOperationWeight])
  simpa only [Batch.sourceEventBudget, ResourcePool.weightedCount, Multiset.map_const',
    Multiset.sum_replicate, Nat.nsmul_eq_mul, Nat.mul_one,
    ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card, modulusBits] using weighted

/-- The literal-classical pool formula is bounded by the complete independent width ceiling. -/
theorem declaredCleanup_classicalOperationBound_le_scalar {N : Nat}
    (input : Input N) (count : Nat) :
    classicalOperationBound input count ≤ scalarClassicalOperationBound N count := by
  cases count with
  | zero => exact le_rfl
  | succ count =>
      have sampler := sampler_classicalWeight_le input
      have recovery := LatticeFixedBatchRecoveryMachine.eventEnvelope_classicalWeight_le
        (model := model input) N
      unfold LatticePairCandidateRecovery.Width LatticeWideLllMachine.Width at recovery
      have batch : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
            (Batch.sourceEventBudget input) +
          ResourcePool.weightedCount Resource.Event.classicalOperationWeight
            (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model input) N) + 35 ≤
          44 * modulusBits N + 198 + LatticeFixedBatchRecoveryMachine.eventCountBound
            (modulusBits N) (shortLogBits N) (tradeoffBits N)
            (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left (count + 1) batch) 1

-- Keep the actual dependent run abstract while using its already established pool bound.

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
