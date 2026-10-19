/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Schedule
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.QuantumTime
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.QuantumTime
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Schedule
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
public import QuantumAlg.Core.Execution.Classical.Predicate
public import QuantumAlg.Core.Execution.Restart
public import QuantumAlg.Core.Execution.Input.Successor
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs

/-!
# Whole-run depth of the canonical all-count EH endpoint

The same bound covers zero trials and every actual first or reused batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

private lemma durationAllowance_le_batchMultiple (N : Nat) (count : Nat)
    (duration : Resource.Event (model N) → Nat) :
    (match count with
      | 0 => Cleanup.durationBudget N duration 0
      | laterCount + 1 => Cleanup.completedDurationBudget N laterCount duration) ≤
      count * Cleanup.twoCompletedMaximumBatchBudget N duration := by
  cases count with
  | zero => simp only [Cleanup.durationBudget, Nat.zero_mul, Nat.le_refl]
  | succ laterCount =>
      change Cleanup.durationBudget N duration 1 +
          laterCount * Cleanup.nextCompletedDurationBudget N duration ≤
        (laterCount + 1) * Cleanup.twoCompletedMaximumBatchBudget N duration
      have first := Nat.le_max_left
        (Cleanup.durationBudget N duration 1)
        (Cleanup.nextCompletedDurationBudget N duration)
      have later := Nat.mul_le_mul_left laterCount (Nat.le_max_right
        (Cleanup.durationBudget N duration 1)
        (Cleanup.nextCompletedDurationBudget N duration))
      change _ ≤ Cleanup.twoCompletedMaximumBatchBudget N duration at first
      change _ ≤ laterCount *
        Cleanup.twoCompletedMaximumBatchBudget N duration at later
      nlinarith

/-- Separate whole-run depth charges every completed batch, including the
classical zero-count branch, under the same arbitrary event clock. -/
public lemma completedAlgorithm_wholeRunDepth_le (input : Input N) (count : Nat)
    (duration : Resource.Event (model N) → Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.depth duration path ≤
      count * Cleanup.twoCompletedMaximumBatchBudget N duration := by
  cases count with
  | zero =>
      have bounded := completedAlgorithm_depth_le
        base noQuantum input 0 duration path
      simpa only [Cleanup.durationBudget, Nat.zero_mul] using bounded
  | succ laterCount =>
      have bounded := completedAlgorithm_depth_le
        base noQuantum input (laterCount + 1) duration path
      exact bounded.trans (durationAllowance_le_batchMultiple N (laterCount + 1) duration)


/-- Independent all-count quantum time includes every member and each one-layer reset.
The zero branch has no quantum work; classical work retains its separate native ledger. -/
public lemma completedAlgorithm_wholeRunQuantumTime_le (input : Input N) (count : Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.quantumTime path ≤
      16 * count * memberQuantumTimeBound N +
        (17 * count - 1) * resetQuantumTime N := by
  cases count with
  | zero =>
      have bounded := completedAlgorithm_depth_le base noQuantum input 0
        Resource.Event.quantumDuration path
      simpa only [Circuit.quantumTime, Cleanup.durationBudget, Nat.zero_mul, Nat.mul_zero,
        Nat.zero_sub, Nat.zero_add] using bounded
  | succ laterCount =>
      change (Cleanup.completedCode base noQuantum N input laterCount).quantumTime path ≤ _
      have bounded := Cleanup.declaredCompleted_quantumTime_le
        base noQuantum N input laterCount path
      have resets : 17 * (laterCount + 1) - 1 = 16 + 17 * laterCount := by omega
      simpa only [Cleanup.completedQuantumTimeBudget, resets] using bounded

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
