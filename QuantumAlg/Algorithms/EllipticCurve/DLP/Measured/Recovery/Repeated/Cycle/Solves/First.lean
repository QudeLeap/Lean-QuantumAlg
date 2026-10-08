/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Probability.Readout.Success.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Borrowed
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Space
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete contract for the first checked ECC section

The same actual run satisfies the independent success, final state,
borrowed restoration, native events, live space and depth clauses.
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

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The original first checked section, with its actual structural readout. -/
def firstCheckedSectionAlgorithm : Algorithm
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  run := firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
    nontrivial (checkedSectionRead E problem)

private theorem firstCheckedSection_pool_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial) (path : code.Path) :
    code.resourcePool path ≤ checkedSectionEventBudget E problem nontrivial := by
  subst code
  exact firstCheckedSection_pool_le E fieldTail sameWidth fits odd problem points
    seed nontrivial path

private theorem firstCheckedSection_resident_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial) (path : code.Path) :
    code.peakResidentSpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).resident := by
  subst code
  exact firstCheckedSection_resident_le E fieldTail sameWidth fits odd problem points
    seed nontrivial path

private theorem firstCheckedSection_auxiliary_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial) (path : code.Path) :
    code.peakAuxiliarySpace path ≤
      (checkedSectionResourceBudget E problem nontrivial).auxiliary := by
  subst code
  exact firstCheckedSection_auxiliary_le E fieldTail sameWidth fits odd problem points
    seed nontrivial path

private theorem firstCheckedSection_depth_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = firstCheckedSectionCode E fieldTail sameWidth fits odd problem
      points seed nontrivial)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : code.Path) :
    (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
      addends).depth.Holds code path := by
  subst code
  exact firstCheckedSection_problemDepth E fieldTail sameWidth fits odd problem
    points seed nontrivial addends path

private theorem firstCheckedSection_solves_of_algorithm
    (algorithm : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (hRun : algorithm.run =
      firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial (checkedSectionRead E problem))
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves algorithm
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends) := by
  have codeEq : algorithm.run.code =
      firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial := by
    rw [hRun]
    rfl
  have readout : algorithm.run.output =
      Output.all _ (checkedSectionRead E problem) := by
    rw [hRun]
    rfl
  constructor
  · intro Reference input valid _
    change (checkedSectionSuccessLB E problem points seed).value ≤
      (algorithm.run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2}
    exact firstCheckedSection_successLB_of_code E problem fieldTail sameWidth fits odd
      points seed nontrivial addends algorithm.run codeEq readout input valid
  · intro Reference input _ _
    rw [hRun]
    exact firstCheckedSection_problemStates E fieldTail sameWidth fits odd problem
      points seed nontrivial addends input
  · intro Reference input _ _
    rw [hRun]
    exact firstCheckedSection_problemBorrowed E fieldTail sameWidth fits odd problem
      points seed nontrivial input
  · intro Reference input _ _ path _
    exact firstCheckedSection_pool_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact firstCheckedSection_resident_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact firstCheckedSection_auxiliary_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact firstCheckedSection_depth_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial algorithm.run.code codeEq addends path

/-- The first checked section solves all seven clauses of its independent problem. -/
theorem firstCheckedSection_solves
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves
      (firstCheckedSectionAlgorithm E fieldTail sameWidth fits odd problem points seed
        nontrivial)
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends) := by
  exact firstCheckedSection_solves_of_algorithm E fieldTail sameWidth fits odd problem
    points seed nontrivial
    (firstCheckedSectionAlgorithm E fieldTail sameWidth fits odd problem points seed
      nontrivial) rfl addends

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
