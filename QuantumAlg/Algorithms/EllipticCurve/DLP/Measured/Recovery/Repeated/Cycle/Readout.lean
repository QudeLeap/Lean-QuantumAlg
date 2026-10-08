/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Cleanup
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Spec
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Readout

/-!
# Fixed physical state at actual checked-section readouts

The first and reused nonterminal sections satisfy the same original sampling
seed at every structural read of their actual store. The readout adds no gate
or allocation; the certified code is the unchanged reset/readout/check/reset.
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

/-- The exact first nonterminal reset/readout/check/next-reset circuit, named
once so its path and native resources have a stable typed interface. -/
def firstCheckedSectionCode :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  (reset.seq body).seq reset

/-- The reused nonterminal circuit starts after the preceding physical reset
and finishes with the next one. -/
def reusedCheckedSectionCode :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) :=
  let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
  let body := (persistentSamplingReadout E fieldTail odd problem points).seq
    (persistentCheckedRecovery E problem nontrivial)
  body.seq reset

/-- Any structural observation of the first actual completed nonterminal
section retains the original specified physical seed after histories sum. -/
theorem firstCheckedSection_readoutPure {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.ReadoutPure
      (⟨((reset.seq body).seq reset), Output.all _ read⟩ : AlgorithmRun _ _ _ shape)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) := by
  dsimp only
  exact Circuit.RestartCleanup.readoutPure _ _
    (firstCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial)

/-- The original first nonterminal reset/readout/check/reset section with a
caller-selected structural output read and a complete live-storage manifest. -/
def firstCheckedSectionRun {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape :=
  ⟨firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial,
    Output.all _ read⟩

/-- The real first nonterminal section satisfies that output-state
requirement after the complete executed history is aggregated. -/
theorem firstCheckedSection_stateRequirement {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    (checkedSectionStateRequirement E fieldTail sameWidth fits problem seed read).Holds
      input.caller
      ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial read).finalState Reference input.state) := by
  let program := firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
    nontrivial read
  have fixed : Circuit.ReinitializedAt program.code
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) :=
    firstCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial
  exact Circuit.RestartCleanup.stateRequirement program
    (persistentSamplingSeed E fieldTail sameWidth fits problem seed) fixed input

/-- The reused nonterminal section uses the same physical reset and complete
structural output manifest after its checked sampling and recovery. -/
def reusedCheckedSectionRun {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape) :
    AlgorithmRun (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape :=
  ⟨reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed nontrivial,
    Output.all _ read⟩

/-- Every reused nonterminal section satisfies the same independently chosen
physical output-state requirement on all admitted reference extensions. -/
theorem reusedCheckedSection_stateRequirement {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    (checkedSectionStateRequirement E fieldTail sameWidth fits problem seed read).Holds
      input.caller
      ((reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
        nontrivial read).finalState Reference input.state) := by
  let program := reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
    nontrivial read
  have fixed : Circuit.ReinitializedAt program.code
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) :=
    reusedCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial
  exact Circuit.RestartCleanup.stateRequirement program
    (persistentSamplingSeed E fieldTail sameWidth fits problem seed) fixed input

/-- The reused nonterminal section has the same actual final-state law. -/
theorem reusedCheckedSection_readoutPure {shape : CShape}
    (read : OutputRead
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) shape) :
    let reset := persistentSamplingReset E fieldTail sameWidth fits problem seed
    let body :=
      (persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)
    Circuit.RestartCleanup.ReadoutPure
      (⟨(body.seq reset), Output.all _ read⟩ : AlgorithmRun _ _ _ shape)
      (persistentSamplingSeed E fieldTail sameWidth fits problem seed) := by
  dsimp only
  exact Circuit.RestartCleanup.readoutPure _ _
    (reusedCheckedSection_reinitializedAt E fieldTail sameWidth fits odd problem
      points seed nontrivial)

/-- The first real section satisfies every final-state requirement of the
independently specified checked-attempt problem, including its actual
accepted/selected readout and complete output-state grouping. -/
theorem firstCheckedSection_problemStates
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    ∀ requirement ∈
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).states,
      requirement.Holds input.caller
        ((firstCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
          nontrivial (checkedSectionRead E problem)).finalState Reference input.state) := by
  intro requirement member
  change requirement ∈
    [checkedSectionStateRequirement E fieldTail sameWidth fits problem seed
      (checkedSectionRead E problem)] at member
  simp only [List.mem_singleton] at member
  subst requirement
  exact firstCheckedSection_stateRequirement E fieldTail sameWidth fits odd problem
    points seed nontrivial (checkedSectionRead E problem) input

/-- The reused real section satisfies the same independent complete
output-state requirement of its seeded-input protocol on every reference extension. -/
theorem reusedCheckedSection_problemStates
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)) Reference) :
    ∀ requirement ∈
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).states,
      requirement.Holds input.caller
        ((reusedCheckedSectionRun E fieldTail sameWidth fits odd problem points seed
          nontrivial (checkedSectionRead E problem)).finalState Reference input.state) := by
  intro requirement member
  change requirement ∈
    [checkedSectionStateRequirement E fieldTail sameWidth fits problem seed
      (checkedSectionRead E problem)] at member
  simp only [List.mem_singleton] at member
  subst requirement
  exact reusedCheckedSection_stateRequirement E fieldTail sameWidth fits odd problem
    points seed nontrivial (checkedSectionRead E problem) input

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
