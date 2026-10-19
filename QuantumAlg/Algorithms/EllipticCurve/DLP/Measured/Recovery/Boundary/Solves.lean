/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.InitializedResources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Seed
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete native initialized-first-cycle contract

The actual prefix and first checked section satisfy all seven clauses of the
independent original-domain protocol: relational success, its nonempty fixed
owned-seed promise, complete borrowed restoration, native events, both live
space peaks and quantum time. The physical carrier is explicitly the reduced
public caller and persistent section; this does not identify it with an older
allocation carrier or establish a whole repeated-run retirement result.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

include sameWidth fits

/-- The complete actual first cycle solves the independent native original-caller problem. -/
lemma initializedFirstCycle_solves (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves
      (initializedAlgorithm E fieldTail problem points seed problem.order
        (Semantics.radixUnit p fieldTail.succ odd) nontrivial)
      (initializedProblem E fieldTail problem points seed nontrivial addends) := by
  constructor
  · intro environment witness Reference input valid _
    exact initialized_success (environment := environment) E fieldTail problem points seed odd
      sameWidth fits nontrivial
      addends input valid
  · intro environment witness Reference input _ _
    exact initialized_problemStates (environment := environment) E fieldTail problem points seed
      problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial addends input
  · intro environment witness Reference input _ _
    exact initialized_borrowed (environment := environment) E fieldTail problem points seed
      problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial input
  · intro environment witness Reference input _ _ path _
    exact (initialized_resources E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial path).1
  · intro environment witness Reference input _ _ path _
    exact (initialized_resources E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial path).2.1
  · intro environment witness Reference input _ _ path _
    exact (initialized_resources E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial path).2.2.1
  · intro environment witness Reference input _ _ path _
    exact (initialized_resources E fieldTail problem points seed problem.order
      (Semantics.radixUnit p fieldTail.succ odd) nontrivial path).2.2.2

/-- Canonical generic instances consume all seven clauses without another caller assumption. -/
lemma algorithm_initializedFirstCycle_solves (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth (ECDLP.Canonical.problem I))
        (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target) :
    Algorithm.Solves
      (initializedAlgorithm E fieldTail (ECDLP.Canonical.problem I) points seed
        (ECDLP.Canonical.problem I).order (Semantics.radixUnit p fieldTail.succ odd)
        I.subgroupOrder_prime.two_le)
      (initializedProblem E fieldTail (ECDLP.Canonical.problem I) points seed
        I.subgroupOrder_prime.two_le addends) :=
  initializedFirstCycle_solves E fieldTail sameWidth fits odd (ECDLP.Canonical.problem I)
    points seed I.subgroupOrder_prime.two_le addends

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
