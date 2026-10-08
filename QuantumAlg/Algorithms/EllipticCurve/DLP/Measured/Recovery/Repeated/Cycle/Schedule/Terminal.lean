/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Terminal.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Schedule.Range
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.FullRun
import all QuantumAlg.Core.Execution.CycleSchedule.Identity

/-!
# Finite checked ECC sections ending in the actual terminal readout

The rotated source code has one final `S;C;id` section, preceded by any
number of real `S;C;R` reused sections. Each predecessor supplies the
terminal or next reused section's seed through its paid physical reset.
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

/-- The original terminal body is an independently certified complete cycle. -/
def terminalCheckedSectionCompleteCycle
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CompleteCycle
      (terminalCheckedSectionCode E fieldTail odd problem points nontrivial)
      (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends) where
  output := Output.all _ (checkedSectionRead E problem)
  certified := terminalCheckedSection_solves E fieldTail sameWidth fits odd problem
    points seed nontrivial addends

/-- The source's final `S;C` is one full cycle, without a following reset. -/
def terminalCheckedSectionSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (.cycle (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends))
      (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) :=
  .complete _ (terminalCheckedSectionCompleteCycle E fieldTail sameWidth fits odd problem
    points seed nontrivial addends)

/-- The actual zero-length range identity after the terminal body is classical. -/
def terminalCheckedTailPlan
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    CyclePlan (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) :=
  .seq (.cycle (terminalCheckedSectionProblem E fieldTail sameWidth fits problem points
    seed nontrivial addends))
    (.classical (Circuit.identityProblem
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (shape := .product .bit (.unsignedWord (orderWidth problem)))
      (sectionCtx E problem) (fun _ => 1) (fun _ => rfl) (fun _ => rfl)))

/-- The last `S;C;id` is certified with its harmless actual range identity. -/
def terminalCheckedTailSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.CycleSchedule
      (terminalCheckedTailPlan E fieldTail sameWidth fits problem points seed nontrivial
        addends)
      ((terminalCheckedSectionCode E fieldTail odd problem points nontrivial).seq
        (Circuit.id (model := .quantum AlgorithmGate.model .empty BitWord.model)
          (sectionCtx E problem))) :=
  .seq _ _
    (terminalCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (Circuit.identitySchedule
      (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (checkedSectionRead E problem)
      (fun _ => 1) (fun _ => rfl) (fun _ => rfl))
    (by intro Reference input admitted; exact ⟨True.intro, True.intro⟩)
    (Or.inl (Circuit.identityClassical (model :=
      .quantum AlgorithmGate.model .empty BitWord.model) (sectionCtx E problem)))

/-- Independent plan for `count` reused physical cycles followed by the
one terminal cycle and its actual classical identity. -/
def reusedTerminalPlan
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : (count : Nat) →
    CyclePlan (.quantum AlgorithmGate.model .empty BitWord.model)
      (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem)))
  | 0 => terminalCheckedTailPlan E fieldTail sameWidth fits problem points seed
      nontrivial addends
  | count + 1 =>
      .seq (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem
        points seed nontrivial addends)) (reusedTerminalPlan addends count)

private theorem reusedTerminalPlan_admits
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) {Reference : Register}
    (input : OracleInput .empty (sectionCtx E problem) Reference) :
    (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial
      addends count).Admits input ↔
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends).Admits input := by
  cases count <;> rfl

/-- Every symbolic reused suffix uses the exact rotated source code and
physical cleanup before its successor, including the terminal cycle. -/
def reusedTerminalSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : (count : Nat) →
    Circuit.CycleSchedule
      (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial
        addends count)
      (Circuit.OperationalEquiv.rotatedTail
        (persistentSamplingReset E fieldTail sameWidth fits problem seed)
        (terminalCheckedSectionCode E fieldTail odd problem points nontrivial) count)
  | 0 => terminalCheckedTailSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends
  | count + 1 =>
      .seq _ _
        (reusedCheckedSectionSchedule E fieldTail sameWidth fits odd problem points
          seed nontrivial addends)
        (reusedTerminalSchedule addends count)
        (by
          intro Reference input admitted
          apply (reusedTerminalPlan_admits E fieldTail sameWidth fits problem points seed
            nontrivial addends count _).mpr
          exact reusedCheckedSection_entryCompatible E fieldTail sameWidth fits odd
            problem points seed nontrivial addends Reference input admitted)
        (Or.inr ⟨reusedCheckedSection_restartCleanup E fieldTail sameWidth fits odd
          problem points seed nontrivial⟩)

/-- One first checked cycle and any finite reused suffix end in the source's
real final readout/check and classical identity. -/
def firstTerminalSchedule
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) (count : Nat) :
    Circuit.CycleSchedule
      (.seq (.cycle (checkedSectionProblem E fieldTail sameWidth fits problem points
        seed nontrivial addends))
        (reusedTerminalPlan E fieldTail sameWidth fits problem points seed nontrivial
          addends count))
      ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial).seq
        (Circuit.OperationalEquiv.rotatedTail
          (persistentSamplingReset E fieldTail sameWidth fits problem seed)
          (terminalCheckedSectionCode E fieldTail odd problem points nontrivial)
          count)) :=
  .seq _ _
    (firstCheckedSectionSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends)
    (reusedTerminalSchedule E fieldTail sameWidth fits odd problem points seed
      nontrivial addends count)
    (by
      intro Reference input admitted
      apply (reusedTerminalPlan_admits E fieldTail sameWidth fits problem points seed
        nontrivial addends count _).mpr
      exact firstCheckedSection_entryCompatible E fieldTail sameWidth fits odd problem
        points seed nontrivial addends Reference input admitted)
    (Or.inr ⟨firstCheckedSection_restartCleanup E fieldTail sameWidth fits odd problem
      points seed nontrivial⟩)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
