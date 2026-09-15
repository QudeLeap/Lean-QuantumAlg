/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight

/-!
# Scalar observations of the actual finite-retry native budget

Every positive batch count pays for one bank preparation, the same sampled
and recovered batch allowance per round, and the final optional selector.
These formulas observe the independent event pool. Their equalities do not
assert that every execution takes every branch listed in that allowance.
Classical operations retain their own literal coordinates and unit weight.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- The first bank preparation is paid once; all batches use the same later-batch allowance. -/
theorem eventEnvelope_succ (N count : Nat) :
    eventEnvelope N (count + 1) =
      ResourcePool.singleton
        (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event +
      (count + 1) • NativeBatchReuseRecovery.eventEnvelope N +
      NativeRetrySelection.selectionEnvelope N (count + 1) := by
  simp only [eventEnvelope, NativeRetrySelection.eventEnvelope, NativeRetryChain.eventEnvelope,
    NativeRetryChain.suffixEventEnvelope, NativeBatchRecovery.eventEnvelope,
    NativeBatch.nativeEnvelope, NativeBatchReuseRecovery.eventEnvelope,
    NativeBatchReuse.nativeEnvelope, succ_nsmul]
  ac_rfl

/-- Every additive native observation has the same preparation, batch and selector formula. -/
theorem eventEnvelope_weighted_succ (N count : Nat) (weight : Resource.Event .quantum → Nat) :
    ResourcePool.weightedCount weight (eventEnvelope N (count + 1)) =
      weight (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event +
      (count + 1) * ResourcePool.weightedCount weight (NativeBatchReuseRecovery.eventEnvelope N) +
      ResourcePool.weightedCount weight
        (NativeRetrySelection.selectionEnvelope N (count + 1)) := by
  rw [eventEnvelope_succ]
  simp only [ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, one_mul]

/-- Closed batch-count formula for the independent total native-event allowance. -/
def eventCountBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 166 +
        16 * (RuntimeRound.eventEnvelope
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).card +
        (LatticeFixedBatchRecoveryMachine.eventEnvelope N : ResourcePool .quantum).card) + 2

/-- Its scalar cardinality pays for the first preparation and the one final pack separately. -/
theorem eventEnvelope_card (N totalRounds : Nat) :
    (eventEnvelope N totalRounds).card = eventCountBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [eventEnvelope_succ]
      simp only [Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate,
        Multiset.card_nsmul, NativeBatchReuseRecovery.eventEnvelope,
        NativeBatchReuse.nativeEnvelope,
        ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card,
        NativeRetrySelection.selectionEnvelope,
        ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card,
        eventCountBound, modulusBits]
      ring

private theorem weighted_mono (weight : Resource.Event .quantum → Nat)
    {left right : ResourcePool .quantum} (bounded : left ≤ right) :
    ResourcePool.weightedCount weight left ≤ ResourcePool.weightedCount weight right := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp bounded
  rw [ResourcePool.weightedCount_add]
  exact Nat.le_add_right _ _

private theorem selector_classicalWeight (N length : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (NativeRetrySelection.selectionEnvelope N length) = 3 * length + 1 := by
  simp [NativeRetrySelection.selectionEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, ResourcePool.scale,
    Resource.Event.classicalOperationWeight, Nat.mul_comm]
  omega

/-- Literal classical-operation count has no charge for the initial quantum preparation. -/
def classicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (NativeBatchReuseRecovery.eventEnvelope N) + 3 * (count + 1) + 1

/-- All repeated classical instructions and the selector contribute their literal unit weights. -/
theorem eventEnvelope_classicalWeight (N totalRounds : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope N totalRounds) = classicalOperationBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [eventEnvelope_weighted_succ, selector_classicalWeight]
      have preparation : Resource.Event.classicalOperationWeight
          (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).event = 0 := rfl
      rw [preparation, zero_add]
      exact (Nat.add_assoc _ _ _).symm

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The scalar native-event allowance bounds each path of the same complete actual run. -/
theorem run_eventCount_le_scalar (specification : Input N) (totalRounds : Nat)
    (path : (run base noQuantum specification totalRounds).code.Path) :
    ((run base noQuantum specification totalRounds).code.eventTrace path).length ≤
      eventCountBound N totalRounds :=
  (run_eventCount_le base noQuantum specification totalRounds path).trans_eq
    (eventEnvelope_card N totalRounds)

/-- The literal classical operations on the same actual path obey the independent scalar formula. -/
theorem run_classicalOperation_le (specification : Input N) (totalRounds : Nat)
    (path : (run base noQuantum specification totalRounds).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum specification totalRounds).code.resourcePool path) ≤
      classicalOperationBound N totalRounds :=
  (weighted_mono Resource.Event.classicalOperationWeight
    (run_pool_le base noQuantum specification totalRounds path)).trans_eq
      (eventEnvelope_classicalWeight N totalRounds)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
