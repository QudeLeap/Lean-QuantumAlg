/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Counts.SameBit

/-!
# Classical cost of independently completed EH batches

Each later batch pays one additional selected-result pack. The physical reset
has no classical-operation event; its measurement and possible correction
remain charged in the separate native event and depth budgets.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution ClassicalRoutines.FirstAccepted.Direct

noncomputable section

private def batchClassicalBound (N : Nat) : Nat :=
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Batch.sourceEventBudget N) +
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (LatticeFixedBatchRecoveryMachine.eventEnvelope (model := model N) N) + 36

private lemma nextCompleted_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (nextCompletedEventBudget N) = batchClassicalBound N := by
  simp only [nextCompletedEventBudget, Retry.nextEventBudget,
    Batch.Recovery.nextEventBudget, Batch.nextEventBudget,
    Batch.reusedSampleEventBudget, reuseEventBudget,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Retry.packEvent, Batch.copyEvent,
    Resource.Event.classicalOperationWeight, batchClassicalBound]
  have member := member_classicalWeight N
  have reset := reset_classicalWeight N
  have selection := selection_classicalWeight N
  simp only [member, reset, selection] at *
  omega

private lemma firstCompleted_classicalWeight (N : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventBudget N 1) = batchClassicalBound N := by
  rw [declaredCleanup_eventBudget_classicalWeight]
  simp [classicalOperationBound, batchClassicalBound]

/-- The literal classical-event allowance is exactly one full source,
recovery, two sample packs, selector and result pack per completed batch. -/
lemma completedEventBudget_classicalWeight (N : Nat)
    (laterCount : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (completedEventBudget N laterCount) =
        (laterCount + 1) * batchClassicalBound N := by
  simp only [completedEventBudget, ResourcePool.scale,
    ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    firstCompleted_classicalWeight, nextCompleted_classicalWeight]
  ring

/-- The complete batch ceiling adds exactly one result-pack instruction to
the accepted scalar first-batch ceiling. -/
lemma batchClassicalBound_le_scalar (N : Nat) :
    batchClassicalBound N ≤
      44 * modulusBits N + 199 +
        LatticeFixedBatchRecoveryMachine.eventCountBound
          (modulusBits N) (shortLogBits N) (tradeoffBits N)
          (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N)) := by
  have first := declaredCleanup_classicalOperationBound_le_scalar N 1
  simp only [classicalOperationBound, scalarClassicalOperationBound] at first
  unfold batchClassicalBound
  omega

/-- The independent one-batch allowance retains the same-bit linear reserve,
including its actual selected-result pack. -/
private lemma batchClassicalBound_le_linear {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    :
    batchClassicalBound pair.modulus ≤ 2 ^ 52 * n + 1 := by
  have scalar := batchClassicalBound_le_scalar pair.modulus
  have oldLinear := declaredCleanup_classicalCeiling_sameBit_le_linear
    pair positive 1
  simp only [scalarClassicalOperationBound] at oldLinear
  omega

/-- Every completed batch pays its own result pack within the linear reserve. -/
lemma completedEventBudget_classicalWeight_le_linear {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (laterCount : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (completedEventBudget pair.modulus laterCount) ≤
        (laterCount + 1) * (2 ^ 52 * n + 1) := by
  rw [completedEventBudget_classicalWeight]
  exact Nat.mul_le_mul_left (laterCount + 1)
    (batchClassicalBound_le_linear pair positive)

private lemma scalarCubicSlack (n : Nat) (positive : 1 ≤ n) :
    2 ^ 52 * n + 1 ≤ 2 ^ 54 * n ^ 3 := by
  have power : n ≤ n ^ 3 := by nlinarith [Nat.le_mul_self n]
  have one : 1 ≤ n ^ 3 := positive.trans power
  omega

/-- The same-bit cubic reserve still covers every added result pack on the
independently completed path. -/
lemma completedEventBudget_classicalWeight_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (laterCount : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (completedEventBudget pair.modulus laterCount) ≤
        2 ^ 54 * (laterCount + 1) * n ^ 3 + 2 := by
  rw [completedEventBudget_classicalWeight]
  have batchLinear := batchClassicalBound_le_linear pair positive
  have scaled : (laterCount + 1) * batchClassicalBound pair.modulus ≤
      2 ^ 54 * (laterCount + 1) * n ^ 3 := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left (laterCount + 1)
        (batchLinear.trans (scalarCubicSlack n positive))
  exact scaled.trans (Nat.le_add_right _ 2)

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
