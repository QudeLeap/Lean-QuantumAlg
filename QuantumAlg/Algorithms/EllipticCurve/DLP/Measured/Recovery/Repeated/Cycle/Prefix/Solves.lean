/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Success
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Resources
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Readout
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Complete first-cycle contract including actual caller initialization

The independent original-caller protocol is proved on the same initialized
checked circuit. Its success, prescribed physical state, borrowed restoration,
events, resident/auxiliary peaks and depth are all mandatory clauses.
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

/-- The named real initialized checked first-cycle algorithm. -/
def initializedFirstCheckedSectionAlgorithm : Algorithm
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  run := initializedFirstCheckedSectionRun E fieldTail sameWidth fits odd problem
    points seed nontrivial

private theorem initializedFirstCheckedSection_states_of_run
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : run.code = initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    (outputEq : run.output = Output.all _ (checkedSectionRead E problem))
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference) :
    ∀ requirement ∈
      (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends).states,
      requirement.Holds input.caller
        (run.finalState Reference input.state) := by
  intro requirement member
  change requirement ∈ [initializedFirstCheckedSectionStateRequirement E fieldTail
    sameWidth fits problem seed] at member
  simp only [List.mem_singleton] at member
  subst requirement
  have fixed : Circuit.ReinitializedAt run.code
      (checkedSectionSeed E fieldTail sameWidth fits problem seed) := by
    rw [codeEq]
    exact Circuit.RestartCleanup.afterAt (checkedRunPrefix E problem)
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial)
      (checkedSectionSeed E fieldTail sameWidth fits problem seed)
      (firstCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem points
        seed nontrivial)
  have observed := Circuit.RestartCleanup.stateRequirement run
    (checkedSectionSeed E fieldTail sameWidth fits problem seed) fixed input
  rw [outputEq] at observed
  exact observed

private theorem initializedFirstCheckedSection_borrowed_of_run
    (run : AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (codeEq : run.code = initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference) :
    run.RestoresBorrowed input := by
  apply AlgorithmRun.restoresBorrowed_of_circuit run ?_ input
  intro Reference H _ state
  rw [codeEq]
  exact (initializedFirstCheckedSection_restartCleanup E fieldTail sameWidth fits odd
    problem points seed nontrivial).restores Reference state

private theorem initializedFirstCheckedSection_bounds_of_code
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem))
    (same : code = initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd
      problem points seed nontrivial) (path : code.Path) :
    code.resourcePool path ≤ initializedFirstCheckedSectionEventBudget E problem nontrivial ∧
    code.peakResidentSpace path ≤ (checkedSectionResourceBudget E problem nontrivial).resident ∧
    code.peakAuxiliarySpace path ≤ (checkedSectionResourceBudget E problem nontrivial).auxiliary ∧
    code.depth (fun _ => 1) path ≤ ResourcePool.weightedCount (fun _ => 1)
      (initializedFirstCheckedSectionEventBudget E problem nontrivial) := by
  subst code
  exact ⟨initializedFirstCheckedSection_pool_le E fieldTail sameWidth fits odd problem
      points seed nontrivial path,
    initializedFirstCheckedSection_resident_le E fieldTail sameWidth fits odd problem
      points seed nontrivial path,
    initializedFirstCheckedSection_auxiliary_le E fieldTail sameWidth fits odd problem
      points seed nontrivial path,
    initializedFirstCheckedSection_depth_le E fieldTail sameWidth fits odd problem
      points seed nontrivial path⟩

private theorem initializedFirstCheckedSection_solves_of_algorithm
    (algorithm : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))))
    (same : algorithm.run = initializedFirstCheckedSectionRun E fieldTail sameWidth fits odd
      problem points seed nontrivial)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves algorithm (initializedFirstCheckedSectionProblem E fieldTail sameWidth
      fits problem points seed nontrivial addends) := by
  have codeEq : algorithm.run.code = initializedFirstCheckedSectionCode E fieldTail sameWidth
      fits odd problem points seed nontrivial := by
    rw [same]
    rfl
  have composite : algorithm.run =
      { code := (checkedRunPrefix E problem).seq
          (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
            nontrivial (checkedSectionRead E problem)).code
        output := (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
          nontrivial (checkedSectionRead E problem)).output } := by
    rw [same]
    rfl
  have outputEq : algorithm.run.output = Output.all _ (checkedSectionRead E problem) := by
    rw [same]
    rfl
  constructor
  · intro Reference input valid _
    change (checkedSectionSuccessLB E problem points seed).value ≤
      (algorithm.run.relationalDistribution input).toOuterMeasure
        (Prod.snd ⁻¹' {value | initializedFirstCheckedSectionAccepts E problem value})
    exact initializedFirstCheckedSection_success_of_runs E fieldTail sameWidth fits odd
      problem points seed nontrivial addends (checkedRunPrefix E problem) rfl
      (firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed nontrivial
        (checkedSectionRead E problem)) rfl rfl algorithm.run composite input valid
  · intro Reference input _ _
    exact initializedFirstCheckedSection_states_of_run E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run codeEq outputEq addends input
  · intro Reference input _ _
    exact initializedFirstCheckedSection_borrowed_of_run E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run codeEq input
  · intro Reference input _ _ path _
    exact (initializedFirstCheckedSection_bounds_of_code E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run.code codeEq path).1
  · intro Reference input _ _ path _
    exact (initializedFirstCheckedSection_bounds_of_code E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run.code codeEq path).2.1
  · intro Reference input _ _ path _
    exact (initializedFirstCheckedSection_bounds_of_code E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run.code codeEq path).2.2.1
  · intro Reference input _ _ path _
    exact (initializedFirstCheckedSection_bounds_of_code E fieldTail sameWidth fits odd
      problem points seed nontrivial algorithm.run.code codeEq path).2.2.2

/-- All seven clauses hold for the actual initialized first cycle on the
original caller domain, without any additional input seed or latch assumption. -/
theorem initializedFirstCheckedSection_solves
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Algorithm.Solves
      (initializedFirstCheckedSectionAlgorithm E fieldTail sameWidth fits odd problem points
        seed nontrivial)
      (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends) := by
  exact initializedFirstCheckedSection_solves_of_algorithm E fieldTail sameWidth fits odd
    problem points seed nontrivial
    (initializedFirstCheckedSectionAlgorithm E fieldTail sameWidth fits odd problem points
      seed nontrivial) rfl addends

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
