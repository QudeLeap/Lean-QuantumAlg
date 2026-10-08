/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Terminal

/-!
# Maximum depth of the actual finite checked ECC suffix

Each complete checked section retains its actual serial depth. The maximum
of those depths fits one independent section allowance for every symbolic
repetition count. The final identity is classical and contributes zero.
The surrounding one-time preparation, allocation and final packing are
separate obligations of the complete algorithm.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The independent unit-duration allowance for one complete checked section. -/
def checkedSectionDepthBudget : Nat :=
  ResourcePool.weightedCount (fun _ => 1)
    (checkedSectionEventBudget E problem nontrivial)

private theorem terminalCheckedSection_commonDepth_le
    (path : (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).Path) :
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial).depth
      (fun _ => 1) path ≤ checkedSectionDepthBudget E problem nontrivial := by
  apply Circuit.depth_le_weightedCount_of_pool_le
    (terminalCheckedSectionCode E fieldTail odd problem points nontrivial)
    (fun _ => 1) (checkedSectionEventBudget E problem nontrivial) path
  exact (terminalCheckedSection_pool_le E fieldTail odd problem points nontrivial
    path).trans (Multiset.le_add_right _ _)

/-- The final actual readout/check and classical range identity fit one
complete-section allowance, without adding a fictitious final reset. -/
theorem terminalCheckedTail_maximumCycleDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : ((terminalCheckedSectionCode E fieldTail odd problem points nontrivial).seq
      (Circuit.id _)).Path) :
    (terminalCheckedTailSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends).maximumCycleDepth (fun _ => 1) path ≤
        checkedSectionDepthBudget E problem nontrivial := by
  change max
    ((terminalCheckedSectionCode E fieldTail odd problem points nontrivial).depth
      (fun _ => 1) path.1) 0 ≤ _
  exact max_le
    (terminalCheckedSection_commonDepth_le E fieldTail odd problem points nontrivial path.1)
    (Nat.zero_le _)

/-- Arbitrarily many reused checked sections followed by the actual terminal
cycle fit the same independent maximum depth, without unrolling the count. -/
theorem reusedTerminal_maximumCycleDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    ∀ path : (Circuit.OperationalEquiv.rotatedTail
      (persistentSamplingReset E fieldTail sameWidth fits problem seed)
      (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) count).Path,
    (reusedTerminalSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count).maximumCycleDepth (fun _ => 1) path ≤
        checkedSectionDepthBudget E problem nontrivial := by
  induction count with
  | zero =>
      exact terminalCheckedTail_maximumCycleDepth_le E fieldTail sameWidth fits odd
        problem points seed nontrivial addends
  | succ count ih =>
      intro path
      change max
        ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial).depth (fun _ => 1) path.1)
        ((reusedTerminalSchedule E fieldTail sameWidth fits odd problem points seed
          nontrivial addends count).maximumCycleDepth (fun _ => 1) path.2) ≤ _
      exact max_le
        (Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path.1
          (reusedCheckedSection_pool_le E fieldTail sameWidth fits odd problem points
            seed nontrivial path.1))
        (ih path.2)

/-- The first physical checked section and the entire terminal suffix obey
one maximum complete-cycle allowance, independently of the finite retry count. -/
theorem firstTerminal_maximumCycleDepth_le
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat)
    (path : ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).seq (Circuit.OperationalEquiv.rotatedTail
        (persistentSamplingReset E fieldTail sameWidth fits problem seed)
        (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) count)).Path) :
    (firstTerminalSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count).maximumCycleDepth (fun _ => 1) path ≤
        checkedSectionDepthBudget E problem nontrivial := by
  change max
    ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
      nontrivial).depth (fun _ => 1) path.1)
    ((reusedTerminalSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count).maximumCycleDepth (fun _ => 1) path.2) ≤ _
  exact max_le
    (Circuit.depth_le_weightedCount_of_pool_le _ (fun _ => 1) _ path.1
      (firstCheckedSection_pool_le E fieldTail sameWidth fits odd problem points seed
        nontrivial path.1))
    (reusedTerminal_maximumCycleDepth_le E fieldTail sameWidth fits odd problem points
      seed nontrivial addends count path.2)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
