/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Admission
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Reused.Cycle
import all QuantumAlg.Core.Execution.CycleSchedule.Identity

/-!
# Actual chronological schedule of reused completed EH batches

The for-range code is right-associated: each real batch precedes the next,
and its zero-length identity tail is a standalone classical section. Exactly
the requested number of quantum cycles appear in this suffix schedule.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
namespace Cleanup

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

private def factorRead : OutputRead (Retry.context base noQuantum N)
    (LatticeBatchRecoveryOutput.OutputShape N) :=
  .read (.storage (Retry.factorRef base noQuantum N).toCStorageRef)

/-- Independent schedule plan for exactly `count` reused batches, followed
by the actual classical identity at the end of `Circuit.forRange`. -/
def laterCompletedCyclePlan : (count : Nat) →
    (duration : Resource.Event (model input) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    CyclePlan (model input) (Retry.context base noQuantum N)
      (Retry.context base noQuantum N)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0, duration, unitQueries =>
      .classical (Circuit.identityProblem (model := model input)
        (shape := LatticeBatchRecoveryOutput.OutputShape N)
        (Retry.context base noQuantum N) duration
        (fun coordinate => nomatch coordinate) unitQueries)
  | count + 1, duration, unitQueries =>
      .seq (.cycle (nextCompletedProblem base noQuantum N input duration unitQueries))
        (laterCompletedCyclePlan count duration unitQueries)

/-- The same actual range circuit implements each independently requested
later batch and its paid physical reset, ending in a zero-event identity. -/
def laterCompletedCycleSchedule : (count : Nat) →
    (duration : Resource.Event (model input) → Nat) →
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) →
    Circuit.CycleSchedule
      (laterCompletedCyclePlan base noQuantum N input count duration unitQueries)
      (laterCompletedCode base noQuantum N input count)
  | 0, duration, unitQueries =>
      Circuit.identitySchedule (model := model input) (Retry.context base noQuantum N)
        (factorRead base noQuantum N) duration
        (fun coordinate => nomatch coordinate) unitQueries
  | count + 1, duration, unitQueries =>
      .seq (nextCompletedCode base noQuantum N input)
        (laterCompletedCode base noQuantum N input count)
        (nextCompletedCycleCertificate base noQuantum N input duration unitQueries).schedule
        (laterCompletedCycleSchedule count duration unitQueries)
        (by
          intro Reference original admitted
          cases count with
          | zero => exact ⟨True.intro, True.intro⟩
          | succ count =>
              exact ⟨True.intro,
                nextCompleted_nextInput_selectedSound base noQuantum N input
                  original admitted.2⟩)
        (Or.inr ⟨nextCompleted_restartCleanup base noQuantum input⟩)

end

end Cleanup
end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Retry.Finite
