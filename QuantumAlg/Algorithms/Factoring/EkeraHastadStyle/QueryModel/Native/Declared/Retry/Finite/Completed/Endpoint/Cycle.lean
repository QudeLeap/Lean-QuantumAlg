/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Schedule
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Depth
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Resources
public import QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Schedule
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Depth
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs

/-!
# Complete-cycle contract on the canonical all-count EH endpoint

The existing `completedAlgorithm` remains the single candidate for zero and
positive total counts. Zero is a classical section; a positive count is the
actual first completed batch followed by exactly the requested reused batches.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The canonical all-count endpoint's independent cycle problem. -/
public def completedCycleProblem (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (count : Nat) → CycleProblem (model input) base (context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => zeroCycleProblem base noQuantum input duration unitQueries
  | laterCount + 1 =>
      Cleanup.completedCycleProblem base noQuantum N input laterCount
        duration unitQueries

/-- The cycle contract's outcome is exactly the existing all-count independent
problem, including the classical zero-count branch. -/
theorem completedCycleProblem_outcome (input : Input N)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (count : Nat) :
    (completedCycleProblem base noQuantum input duration unitQueries count).outcome =
      completedAllProblem base noQuantum input duration unitQueries count := by
  cases count <;> rfl

/-- The existing all-count endpoint has an actual complete-cycle schedule
and all-input source/state/resource correctness at every requested count. -/
public def completedAlgorithmCycleSolves (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (completedAlgorithm base noQuantum input count)
      (completedCycleProblem base noQuantum input duration unitQueries count) :=
  match count with
  | 0 => zeroCycleCertificate base noQuantum input duration unitQueries
  | laterCount + 1 =>
      Cleanup.completedCycleCertificate base noQuantum N input laterCount
        duration unitQueries

/-- The actual all-count endpoint's maximum complete-cycle depth is zero for
the purely classical branch and otherwise bounded by the larger of the two
independent completed-batch allowances, regardless of batch count. -/
public theorem completedAlgorithm_maximumCycleDepth_le (input : Input N)
    (count : Nat) (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    Algorithm.CycleSolves.maximumCycleDepth
      (completedAlgorithmCycleSolves base noQuantum input count duration unitQueries)
      duration path ≤
        match count with
        | 0 => 0
        | _ + 1 =>
            Cleanup.twoCompletedMaximumBatchBudget input duration := by
  cases count with
  | zero => rfl
  | succ laterCount =>
      exact Cleanup.completedCycleDepth_le base noQuantum N input
        laterCount duration unitQueries path

/-- A positive completed count has the same independent two-batch maximum
cycle allowance, without exposing the zero-count path branch to consumers. -/
public theorem completedAlgorithm_maximumCycleDepth_le_positive (input : Input N)
    (count : Nat) (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (positive : 0 < count)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    Algorithm.CycleSolves.maximumCycleDepth
      (completedAlgorithmCycleSolves base noQuantum input count duration unitQueries)
      duration path ≤
        Cleanup.twoCompletedMaximumBatchBudget input duration := by
  cases count with
  | zero => omega
  | succ laterCount =>
      exact completedAlgorithm_maximumCycleDepth_le
        base noQuantum input (laterCount + 1) duration unitQueries path


private theorem durationAllowance_le_cycleMultiple {N : Nat} (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat) :
    (match count with
      | 0 => Cleanup.durationBudget input duration 0
      | laterCount + 1 => Cleanup.completedDurationBudget N input laterCount duration) ≤
      count * Cleanup.twoCompletedMaximumBatchBudget input duration := by
  cases count with
  | zero => simp only [Cleanup.durationBudget, Nat.zero_mul, Nat.le_refl]
  | succ laterCount =>
      change Cleanup.durationBudget input duration 1 +
          laterCount * Cleanup.nextCompletedDurationBudget input duration ≤
        (laterCount + 1) * Cleanup.twoCompletedMaximumBatchBudget input duration
      have first := Nat.le_max_left
        (Cleanup.durationBudget input duration 1)
        (Cleanup.nextCompletedDurationBudget input duration)
      have later := Nat.mul_le_mul_left laterCount (Nat.le_max_right
        (Cleanup.durationBudget input duration 1)
        (Cleanup.nextCompletedDurationBudget input duration))
      change _ ≤ Cleanup.twoCompletedMaximumBatchBudget input duration at first
      change _ ≤ laterCount *
        Cleanup.twoCompletedMaximumBatchBudget input duration at later
      nlinarith

/-- Separate whole-run depth charges every completed batch, including the
classical zero-count branch, under the same arbitrary event clock. -/
public theorem completedAlgorithm_wholeRunDepth_le (input : Input N) (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (path : (completedAlgorithm base noQuantum input count).run.code.Path) :
    (completedAlgorithm base noQuantum input count).run.code.depth duration path ≤
      count * Cleanup.twoCompletedMaximumBatchBudget input duration := by
  cases count with
  | zero =>
      have bounded := completedAlgorithm_depth_le
        base noQuantum input 0 duration path
      simpa only [Cleanup.durationBudget, Nat.zero_mul] using bounded
  | succ laterCount =>
      have bounded := completedAlgorithm_depth_le
        base noQuantum input (laterCount + 1) duration path
      exact bounded.trans (durationAllowance_le_cycleMultiple input (laterCount + 1) duration)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
