/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Admission

/-!
# Original generic ECC input admits the first checked section

The generic problem's caller domain supplies precisely its public points.
The actual prefix establishes the retained-selection invariant itself.
This theorem adds no extra input condition and quantifies every admitted
external reference extension of the original caller.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Every admitted original caller enters the first checked-section protocol
after the actual one-time initialization and seven-cell allocation. -/
theorem algorithm_prefix_admits_checkedSection
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (addends : AddendEncoding E I points)
    (count : Nat) (failure : ℝ) {Reference : Register}
    (input : OracleInput .empty (inputContext E I) Reference)
    (admitted : (problem E I count failure).Admits input) :
    (checkedSectionProblem E fieldTail sameWidth fits (ECDLP.Canonical.problem I)
      points seed I.subgroupOrder_prime.two_le addends).Admits
        ((checkedRunPrefix E (ECDLP.Canonical.problem I)).nextInput input) := by
  exact ⟨checkedRunPrefix_nextInput_domain E (ECDLP.Canonical.problem I)
    I.subgroupOrder_prime.two_le input admitted.1, True.intro⟩

end

end QuantumAlg.EllipticCurve.LogicalResources
