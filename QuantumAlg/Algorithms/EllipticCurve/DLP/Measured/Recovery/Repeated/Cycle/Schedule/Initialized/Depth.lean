/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Initialized
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Depth
import all QuantumAlg.Core.Execution.CycleSchedule.Bounds

/-!
# Maximum complete-cycle depth including the original ECC initialization

The independent first-cycle allowance includes the real one-time prefix.
All later checked cycles fit their common allowance for every symbolic retry
count. Their maximum is retained on actual source paths by structural
regrouping; the real final option pack remains in chronological execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] Circuit.CycleSchedule.maximumCycleDepth

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- Parameter-only complete-cycle allowance including the real initial prefix. -/
def initializedRepeatedDepthBudget : Nat :=
  max (ResourcePool.weightedCount (fun _ => 1)
    (initializedFirstCheckedSectionEventBudget E problem nontrivial))
    (checkedSectionDepthBudget E problem nontrivial)

/-- Initialization and every later real cycle obey their independent maximum. -/
theorem initializedFirstTerminal_maximumCycleDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat)
    (path : ((initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial).seq (Circuit.OperationalEquiv.rotatedTail
        (persistentSamplingReset E fieldTail sameWidth fits problem seed)
        (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) count)).Path) :
    (initializedFirstTerminalSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count).maximumCycleDepth (fun _ => 1) path ≤
        initializedRepeatedDepthBudget E problem nontrivial := by
  unfold initializedFirstTerminalSchedule
  apply Circuit.CycleSchedule.maximumCycleDepth_seq_le
  · intro firstPath
    exact (initializedFirstCheckedSection_maximumDepth_le E fieldTail sameWidth fits odd
      problem points seed nontrivial addends firstPath).trans (Nat.le_max_left _ _)
  · intro suffixPath
    exact (reusedTerminal_maximumCycleDepth_le E fieldTail sameWidth fits odd problem points
      seed nontrivial addends count suffixPath).trans (Nat.le_max_right _ _)

/-- The full source schedule has the same bound on every actual original run
path, with final packing preserved and no retry-count expansion. -/
theorem exponentRepeatedRun_initializedMaximumCycleDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat)
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial ((count + 1) + 1)).code.Path) :
    (exponentRepeatedRun_initializedSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count).maximumCycleDepth (fun _ => 1) path ≤
        initializedRepeatedDepthBudget E problem nontrivial := by
  unfold exponentRepeatedRun_initializedSchedule
  apply Circuit.CycleSchedule.maximumCycleDepth_reassociate_le
  apply Circuit.CycleSchedule.maximumCycleDepth_seq_le
  · exact initializedFirstTerminal_maximumCycleDepth_le E fieldTail sameWidth fits odd
      problem points seed nontrivial addends count
  · intro packedPath
    simp only [BatchPacking.schedule, Circuit.CycleSchedule.maximumCycleDepth_classical]
    exact Nat.zero_le _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
