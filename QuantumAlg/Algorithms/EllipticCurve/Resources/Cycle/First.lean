/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Schedule

/-!
# Generic ECC consumer of the complete initialized first cycle

Every original admitted generic ECC caller is admitted by the complete first
cycle, whose seven correctness/resource clauses and actual schedule are
proved together. This is a first-cycle certificate, separate from the
remaining finite whole-run composition and final option packing.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The original generic domain admits the independently specified first
cycle, without additional caller state, latch, or seed hypotheses. -/
theorem algorithm_admits_initializedFirstCycle
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ) {Reference : Register}
    (input : OracleInput .empty (inputContext E I) Reference)
    (admitted : (problem E I count failure).Admits input) :
    (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits (ECDLP.Canonical.problem I)
      points seed I.subgroupOrder_prime.two_le addends).Admits input :=
  ⟨admitted.1, True.intro⟩

/-- The canonical generic instance consumes all seven first-cycle clauses
on the actual original-caller algorithm, before any fixed-width specialization. -/
theorem algorithm_initializedFirstCycle_solves
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points) :
    Algorithm.Solves
      (initializedFirstCheckedSectionAlgorithm E fieldTail sameWidth fits odd
        (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le)
      (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits (ECDLP.Canonical.problem I)
        points seed I.subgroupOrder_prime.two_le addends) :=
  initializedFirstCheckedSection_solves E fieldTail sameWidth fits odd
    (ECDLP.Canonical.problem I) points seed I.subgroupOrder_prime.two_le addends

end

end QuantumAlg.EllipticCurve.LogicalResources
