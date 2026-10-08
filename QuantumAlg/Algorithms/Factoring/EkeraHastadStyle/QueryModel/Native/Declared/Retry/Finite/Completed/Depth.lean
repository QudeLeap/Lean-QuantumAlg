/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Schedule

/-!
# Maximum complete-cycle depth of the actual EH completed-batch schedule

Each paid batch carries its own serial depth. The complete-cycle coordinate is
their maximum, while `completedFiniteAlgorithm_depth_le` separately preserves
the chronological whole-run depth and all classical work.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private theorem laterCompletedCycleDepth_zero
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (laterCompletedCode base noQuantum N input 0).Path) :
    (laterCompletedCycleSchedule base noQuantum N input 0 duration unitQueries).maximumCycleDepth
      duration path = 0 := rfl

private theorem laterCompletedCycleDepth_succ (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (laterCompletedCode base noQuantum N input (count + 1)).Path) :
    (laterCompletedCycleSchedule base noQuantum N input (count + 1)
      duration unitQueries).maximumCycleDepth duration path =
      max ((nextCompletedCode base noQuantum N input).depth duration path.1)
        ((laterCompletedCycleSchedule base noQuantum N input count
          duration unitQueries).maximumCycleDepth duration path.2) := rfl

/-- Each real later cycle obeys its own batch allowance, with the actual
zero-length identity tail contributing zero complete-cycle depth. -/
theorem laterCompletedCycleDepth_le (count : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    ∀ path : (laterCompletedCode base noQuantum N input count).Path,
      Circuit.CycleSchedule.maximumCycleDepth
        (laterCompletedCycleSchedule base noQuantum N input count duration unitQueries)
        duration path ≤ nextCompletedDurationBudget input duration := by
  induction count with
  | zero =>
      intro path
      rw [laterCompletedCycleDepth_zero base noQuantum N input duration unitQueries path]
      exact Nat.zero_le _
  | succ count ih =>
      intro path
      rw [laterCompletedCycleDepth_succ base noQuantum N input count duration
        unitQueries path]
      exact max_le (nextCompleted_depth_le base noQuantum N input duration path.1)
        (ih path.2)

/-- The actual finite run has one complete cycle for the first batch and one
for each reused batch. Its cycle depth is bounded by the larger complete
batch allowance, independently of how many batches are scheduled. -/
theorem completedCycleDepth_le (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (completedFiniteAlgorithm base noQuantum input laterCount).run.code.Path) :
    Algorithm.CycleSolves.maximumCycleDepth
      (completedCycleCertificate base noQuantum N input laterCount duration unitQueries)
      duration path ≤
        max (Cleanup.durationBudget input duration 1)
          (nextCompletedDurationBudget input duration) := by
  change max
    ((firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1)
    (Circuit.CycleSchedule.maximumCycleDepth
      (laterCompletedCycleSchedule base noQuantum N input laterCount duration unitQueries)
      duration path.2) ≤ _
  apply max_le
  · exact (firstCompleted_depth_le base noQuantum input duration path.1).trans
      (le_max_left _ _)
  · exact (laterCompletedCycleDepth_le base noQuantum N input laterCount
      duration unitQueries path.2).trans (le_max_right _ _)

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
