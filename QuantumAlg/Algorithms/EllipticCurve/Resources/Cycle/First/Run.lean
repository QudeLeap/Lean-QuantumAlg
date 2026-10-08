/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.FullRun

/-!
# Complete initialized first-cycle depth on actual generic ECC paths

The exact full execution correspondence supplies the original initialization,
allocation and first checked-cycle path from every path of the named generic
algorithm. The certified depth coordinate counts this entire first cycle.
The remaining suffix schedule and final packing still require whole-run
composition; this coordinate alone is not full algorithm-cycle acceptance.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
  (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
  (seed : AffinePoint E) (addends : AddendEncoding E I points)

/-- The complete initialized first cycle's certified depth on a real path
of the original generic algorithm, including its one-time prefix. -/
def checkedInitializedFirstMaximumDepth (count : Nat)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed
      ((count + 1) + 1)).run.code.Path) : Nat :=
  (initializedFirstCheckedSectionSchedule E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends).maximumCycleDepth
      (fun _ => 1)
      ((exponentRepeatedRun_initializedFirstCycle E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count).path path).1.1

/-- The actual generic algorithm consumes the complete initialized first
cycle bound symbolically, before any fixed width or count is evaluated. -/
theorem algorithm_checkedInitializedFirst_maximumDepth_le (count : Nat)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed
      ((count + 1) + 1)).run.code.Path) :
    checkedInitializedFirstMaximumDepth E fieldTail sameWidth fits odd I points seed addends
      count path ≤ ResourcePool.weightedCount (fun _ => 1)
        (initializedFirstCheckedSectionEventBudget E (ECDLP.Canonical.problem I)
          I.subgroupOrder_prime.two_le) := by
  unfold checkedInitializedFirstMaximumDepth
  generalize ((exponentRepeatedRun_initializedFirstCycle E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count).path path).1.1 =
      firstPath
  exact initializedFirstCheckedSection_maximumDepth_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends firstPath

end

end QuantumAlg.EllipticCurve.LogicalResources
