/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Depth

/-!
# Checked-cycle suffix on the named generic ECDLP execution

The exact operational equivalence supplies the suffix path from every path
of the original generic algorithm. Its completed checked cycles have a
maximum depth independent of the finite retry count. This suffix coordinate
does not include the one-time initialization and persistent allocation;
those must be included in the first cycle of a complete algorithm schedule.
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

/-- Maximum depth of the certified checked suffix on the original algorithm
path, retaining the exact path correspondence of the complete execution. -/
def checkedSuffixMaximumDepth (count : Nat)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed
      ((count + 1) + 1)).run.code.Path) : Nat :=
  (firstTerminalSchedule E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder_prime.two_le addends count).maximumCycleDepth
      (fun _ => 1)
      ((exponentRepeatedRun_firstCycle E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count).path
          path).2.1.2

/-- The named generic algorithm consumes the symbolic suffix theorem on its
own actual paths. No fixed curve width or concrete repetition count is expanded. -/
theorem algorithm_checkedSuffix_maximumDepth_le (count : Nat)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed
      ((count + 1) + 1)).run.code.Path) :
    checkedSuffixMaximumDepth E fieldTail sameWidth fits odd I points seed addends
      count path ≤ checkedSectionDepthBudget E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le :=
  firstTerminal_maximumCycleDepth_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends count
    ((exponentRepeatedRun_firstCycle E fieldTail sameWidth fits odd
      (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le count).path
        path).2.1.2

end

end QuantumAlg.EllipticCurve.LogicalResources
