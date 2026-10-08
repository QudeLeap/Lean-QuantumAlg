/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Repeated
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Path

/-!
# Independent event and serial-duration bounds for completed EH batches

The first completed batch and each further completed same-bank batch pay
their own pack and physical reset. These formulas are independent of the
executed path. The complete-cycle maximum and resident-space contract are
separate obligations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- Every further completed batch is charged the same complete independent
event allowance, including its additional pack and reset. -/
def completedEventBudget (laterCount : Nat) : ResourcePool (model input) :=
  eventBudget input 1 + ResourcePool.scale laterCount (nextCompletedEventBudget input)

/-- Whole-run serial duration adds every batch's actual internal dependencies. -/
def completedDurationBudget (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat) : Nat :=
  durationBudget input duration 1 +
    laterCount * nextCompletedDurationBudget input duration

/-- The actual complete path is the first batch followed by every projected
later batch trace in chronological order; no reset or pack is hidden. -/
theorem completed_eventTrace_eq (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).eventTrace path =
      (firstCompletedAlgorithm base noQuantum input).run.code.eventTrace path.1 ++
        (List.ofFn fun index : Fin laterCount =>
          (nextCompletedCode base noQuantum N input).eventTrace
            (Circuit.forRangeComponentPath laterCount
              (fun _ => nextCompletedCode base noQuantum N input) path.2 index)).flatten := by
  change (firstCompletedAlgorithm base noQuantum input).run.code.eventTrace path.1 ++
    (laterCompletedCode base noQuantum N input laterCount).eventTrace path.2 = _
  exact congrArg
    (fun trace =>
      (firstCompletedAlgorithm base noQuantum input).run.code.eventTrace path.1 ++ trace)
    (Circuit.forRange_eventTrace_eq laterCount
      (fun _ => nextCompletedCode base noQuantum N input) path.2)

/-- The same projected paths add actual internal dependency depths. -/
theorem completed_depth_eq (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).depth duration path =
      (firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1 +
        ∑ index : Fin laterCount,
          (nextCompletedCode base noQuantum N input).depth duration
            (Circuit.forRangeComponentPath laterCount
              (fun _ => nextCompletedCode base noQuantum N input) path.2 index) := by
  change (firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1 +
    (laterCompletedCode base noQuantum N input laterCount).depth duration path.2 = _
  exact congrArg
    (fun depth =>
      (firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1 + depth)
    (Circuit.forRange_depth_eq_sum laterCount
      (fun _ => nextCompletedCode base noQuantum N input) duration path.2)

/-- The actual repeated code obeys its independently stated full event pool
for every path and every original input. -/
theorem completed_resourcePool_le (laterCount : Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).resourcePool path ≤
      completedEventBudget N input laterCount := by
  have tail := Circuit.forRange_pool_le laterCount
    (fun _ => nextCompletedCode base noQuantum N input)
    (nextCompletedEventBudget input)
    (fun _ => nextCompleted_resourcePool_le base noQuantum N input) path.2
  change (firstCompletedAlgorithm base noQuantum input).run.code.resourcePool path.1 +
    (laterCompletedCode base noQuantum N input laterCount).resourcePool path.2 ≤ _
  exact add_le_add (firstCompleted_resourcePool_le base noQuantum input path.1)
    tail

/-- Whole-run depth counts the first complete batch and each real later
completed batch in sequence, for arbitrary event durations. -/
theorem completed_depth_le (laterCount : Nat)
    (duration : Resource.Event (model input) → Nat)
    (path : (completedCode base noQuantum N input laterCount).Path) :
    (completedCode base noQuantum N input laterCount).depth duration path ≤
      completedDurationBudget N input laterCount duration := by
  have tail := Circuit.forRange_depth_le_sum laterCount
    (fun _ => nextCompletedCode base noQuantum N input) duration
    (fun _ => nextCompletedDurationBudget input duration)
    (fun _ => nextCompleted_depth_le base noQuantum N input duration) path.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at tail
  change (firstCompletedAlgorithm base noQuantum input).run.code.depth duration path.1 +
    (laterCompletedCode base noQuantum N input laterCount).depth duration path.2 ≤ _
  exact Nat.add_le_add
    (firstCompleted_depth_le base noQuantum input duration path.1) tail

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
