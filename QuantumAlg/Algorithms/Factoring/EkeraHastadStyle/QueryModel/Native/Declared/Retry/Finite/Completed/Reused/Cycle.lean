/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Solves
import all QuantumAlg.Core.Execution.CycleSchedule

/-!
# An independently certified reused EH batch cycle

The successor batch consumes a sound live selector, retains the original bank,
and completes its own recovery, pack and physical reset before another batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- The independently stated contract of one further completed batch. -/
def nextCompletedCycleProblem
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (model input) (Retry.context base noQuantum N)
      (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N) where
  outcome := nextCompletedProblem base noQuantum N input duration unitQueries
  plan := .cycle (nextCompletedProblem base noQuantum N input duration unitQueries)

/-- The actual next-batch code meets the input-based complete-cycle contract. -/
def nextCompletedCycleCertificate
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (nextCompletedAlgorithm base noQuantum N input)
      (nextCompletedCycleProblem base noQuantum N input duration unitQueries) where
  correctness := nextCompletedAlgorithm_solves base noQuantum N input duration unitQueries
  schedule := .complete (nextCompletedCode base noQuantum N input)
    { output := (nextCompletedRun base noQuantum N input).output
      certified := nextCompletedAlgorithm_solves
        base noQuantum N input duration unitQueries }
  entry := fun _ _ admitted => admitted

/-- A reused batch charges its own complete serial execution to its cycle. -/
theorem nextCompletedCycleDepth_le
    (duration : Resource.Event (model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (nextCompletedCode base noQuantum N input).Path) :
    (nextCompletedCycleCertificate base noQuantum N input duration unitQueries).maximumCycleDepth
      duration path ≤
        nextCompletedDurationBudget input duration := by
  change (nextCompletedCode base noQuantum N input).depth duration path ≤ _
  exact nextCompleted_depth_le base noQuantum N input duration path

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
