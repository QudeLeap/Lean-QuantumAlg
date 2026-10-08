/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Initialized
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Initialized.Depth

/-!
# Same-run generic ECC maximum complete-cycle bound

The complete certificate on the named original algorithm supplies its actual
cycle-depth coordinate, not a suffix proxy. The symbolic allowance includes
initialization and bounds every subsequent completed computation. Its scalar
polynomial conversion and the zero/one-count plans are separate obligations.
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

/-- The actual generic algorithm's complete cycle certificate carries the
independent maximum, on the same run as its original correctness guarantee. -/
theorem algorithm_initializedMaximumCycleDepth_le (count : Nat) (failure : ℝ)
    (calibrated : RepetitionCondition E I points seed ((count + 1) + 1) failure)
    (path : (algorithm E fieldTail sameWidth fits odd I points seed
      ((count + 1) + 1)).run.code.Path) :
    (initializedCycleCertificate E fieldTail sameWidth fits odd I points seed addends
      count failure calibrated).maximumCycleDepth (fun _ => 1) path ≤
        initializedRepeatedDepthBudget E (ECDLP.Canonical.problem I)
          I.subgroupOrder_prime.two_le := by
  change (exponentRepeatedRun_initializedSchedule E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends
      count).maximumCycleDepth (fun _ => 1) path ≤ _
  exact exponentRepeatedRun_initializedMaximumCycleDepth_le E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends count path

end

end QuantumAlg.EllipticCurve.LogicalResources
