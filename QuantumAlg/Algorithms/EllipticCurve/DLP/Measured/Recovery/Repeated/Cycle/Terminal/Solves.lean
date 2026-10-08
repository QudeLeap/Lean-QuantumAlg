/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Terminal.Resources
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Complete contract for the terminal checked ECC section

The actual last readout/check satisfies the independent seeded success,
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

/-- The final checked body with its actual accepted/selected readout. -/
def terminalCheckedSectionAlgorithm : Algorithm
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  run := terminalCheckedSectionRun E fieldTail odd problem points nontrivial

private theorem terminalCheckedSection_pool_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial) (path : code.Path) :
    code.resourcePool path ≤ terminalCheckedSectionEventBudget E problem nontrivial := by
  subst code
  exact terminalCheckedSection_pool_le E fieldTail odd problem points nontrivial path

private theorem terminalCheckedSection_resident_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial) (path : code.Path) :
    code.peakResidentSpace path ≤
      (terminalCheckedSectionResourceBudget E problem nontrivial).resident := by
  subst code
  exact terminalCheckedSection_resident_le E fieldTail odd problem points nontrivial path

private theorem terminalCheckedSection_auxiliary_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial) (path : code.Path) :
    code.peakAuxiliarySpace path ≤
      (terminalCheckedSectionResourceBudget E problem nontrivial).auxiliary := by
  subst code
  exact terminalCheckedSection_auxiliary_le E fieldTail odd problem points nontrivial path

private theorem terminalCheckedSection_depth_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem))
    (codeEq : code = terminalCheckedSectionCode E fieldTail odd problem points
      nontrivial)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    (path : code.Path) :
    (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
      addends).depth.Holds code path := by
  subst code
  exact terminalCheckedSection_problemDepth E fieldTail sameWidth fits odd problem
    points seed nontrivial addends path

private theorem terminalCheckedSection_solves_of_algorithm
    (algorithm : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (hRun : algorithm.run =
      terminalCheckedSectionRun E fieldTail odd problem points nontrivial)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves algorithm
      (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends) := by
  have codeEq : algorithm.run.code =
      terminalCheckedSectionCode E fieldTail odd problem points nontrivial := by
    rw [hRun]
    rfl
  have readout : algorithm.run.output =
      Output.all _ (checkedSectionRead E problem) := by
    rw [hRun]
    rfl
  constructor
  · intro Reference input valid seeded
    change (checkedSectionSuccessLB E problem points seed).value ≤
      (algorithm.run.relationalDistribution input).toOuterMeasure
        {pair | checkedSectionAccepts E problem pair.1 pair.2}
    exact terminalCheckedSection_successLB_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial addends algorithm.run codeEq readout input valid seeded
  · intro Reference input _ _ requirement member
    change requirement ∈ ([] : List (StateRequirement (sectionCtx E problem)
      (sectionCtx E problem))) at member
    exact False.elim (List.not_mem_nil member)
  · intro Reference input _ _
    rw [hRun]
    exact terminalCheckedSection_problemBorrowed E fieldTail odd problem points
      nontrivial input
  · intro Reference input _ _ path _
    exact terminalCheckedSection_pool_of_code E fieldTail odd problem points
      nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact terminalCheckedSection_resident_of_code E fieldTail odd problem points
      nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact terminalCheckedSection_auxiliary_of_code E fieldTail odd problem points
      nontrivial algorithm.run.code codeEq path
  · intro Reference input _ _ path _
    exact terminalCheckedSection_depth_of_code E fieldTail sameWidth fits odd problem
      points seed nontrivial algorithm.run.code codeEq addends path

/-- The original terminal checked body solves its seven-clause seeded protocol. -/
theorem terminalCheckedSection_solves
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves
      (terminalCheckedSectionAlgorithm E fieldTail odd problem points nontrivial)
      (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends) := by
  exact terminalCheckedSection_solves_of_algorithm E fieldTail sameWidth fits odd problem
    points seed nontrivial
    (terminalCheckedSectionAlgorithm E fieldTail odd problem points nontrivial) rfl addends

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
