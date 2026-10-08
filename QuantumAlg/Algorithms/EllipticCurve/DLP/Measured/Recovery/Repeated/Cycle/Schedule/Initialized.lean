/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Prefix.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Terminal
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Reassociation
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing.Solves

/-!
# Complete initialized finite schedules on the original ECC circuit

The first computation includes its real one-time initialization. Every
nonterminal computation supplies the next computation's admitted input and
fixed quantum seed through its actual reset. The terminal checked body has
no following reset; its real option-pack tail is accounted as classical.
Only structural regrouping of the same instructions transports the schedule
back to the original named run, for an arbitrary symbolic attempt count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] Circuit.nextInput

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- The first actual initialized cycle supplies every symbolic reused/terminal suffix. -/
def initializedFirstTerminalSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    Circuit.CycleSchedule
      (.seq (.cycle (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits
        problem points seed nontrivial addends))
        (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial
          addends count))
      ((initializedFirstCheckedSectionCode E fieldTail sameWidth fits odd problem points
        seed nontrivial).seq
        (Circuit.OperationalEquiv.rotatedTail
          (persistentSamplingReset E fieldTail sameWidth fits problem seed)
          (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) count)) :=
  .seq _ _
    (initializedFirstCheckedSectionSchedule E fieldTail sameWidth fits odd problem points
      seed nontrivial addends)
    (reusedTerminalSchedule E fieldTail sameWidth fits odd problem points seed nontrivial
      addends count)
    (by
      have suffixAdmission : ∀ {Reference : Register}
          (input : OracleInput .empty (sectionCtx E problem) Reference),
          (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial
            addends count).Admits input ↔
          (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
            nontrivial addends).Admits input := by
        intro Reference input
        cases count <;> rfl
      intro Reference input admitted
      apply (suffixAdmission _).mpr
      exact ⟨initializedFirstCheckedSection_nextInput_domain E fieldTail sameWidth fits odd
        problem points seed nontrivial input admitted.1,
        initializedFirstCheckedSection_nextInput_seeded E fieldTail sameWidth fits odd
          problem points seed nontrivial input⟩)
    (Or.inr ⟨initializedFirstCheckedSection_restartCleanup E fieldTail sameWidth fits odd
      problem points seed nontrivial⟩)

/-- The independent initialized finite plan includes the terminal paid option pack. -/
def initializedRepeatedPlan
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    CyclePlan (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.before E (orderWidth problem))
      (batchResultCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (.option (.unsignedWord (orderWidth problem))) :=
  .seq
    (.seq (.cycle (initializedFirstCheckedSectionProblem E fieldTail sameWidth fits problem
      points seed nontrivial addends))
      (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial addends count))
    (.classical (BatchPacking.problem
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem)))

/-- The exact original full named run realizes the fixed finite plan, with
initialization, all real computation boundaries and final packing retained. -/
def exponentRepeatedRun_initializedSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    Circuit.CycleSchedule
      (initializedRepeatedPlan E fieldTail sameWidth fits problem points seed nontrivial
        addends count)
      (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed nontrivial
        ((count + 1) + 1)).code :=
  .reassociate
    (exponentRepeatedRun_initializedFirstReassociation E fieldTail sameWidth fits odd
      problem points seed nontrivial count)
    (.seq _ _
      (initializedFirstTerminalSchedule E fieldTail sameWidth fits odd problem points seed
        nontrivial addends count)
      (BatchPacking.schedule (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (by intro Reference input admitted; exact ⟨True.intro, True.intro⟩)
      (Or.inl (BatchPacking.onlyClassical
        (model := .quantum AlgorithmGate.model .empty BitWord.model)
        (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))))

/-- The fixed initialized plan admits exactly the original public caller;
no bank, physical seed or separately initialized service premise is added. -/
theorem initializedRepeatedPlan_admits
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (PublicInput.before E (orderWidth problem)) Reference) :
    (initializedRepeatedPlan E fieldTail sameWidth fits problem points seed nontrivial
      addends count).Admits input ↔
      PublicInput.inputDomain E (orderWidth problem) problem input.caller.localState :=
  ⟨fun admitted => admitted.1, fun valid => ⟨valid, True.intro⟩⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
