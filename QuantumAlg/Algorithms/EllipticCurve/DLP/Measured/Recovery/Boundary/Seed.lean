/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Restart.Embedding
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Latches
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Cleanup
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Cleanup
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding.Restart
import all QuantumAlg.Core.Execution.Restart.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Frame
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained

/-!
# Fixed physical seeds at both actual native boundaries

The reset label is the one declared independently in BoundarySpec. Native
public placement, language selection and the seven-cell persistent placement
transport its actual all-record reset proof in that order. No input-state
seed, separable Reference, positive branch or normalized fiber is assumed.

The first section starts with its own reset. The reused section starts at the
previous physical reset; both finish with the next one. Their output promise
and actual nextInput joint seed are therefore proved independently of success.
Boundary.Solves uses these state promises in the initialized first-cycle contract.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

private lemma reinitialized_with_persistent_seed {ctx : RuntimeCtx .quantum}
    (code : Circuit Model ctx ctx false) (width scalarWidth : Nat)
    (label : ctx.register.Index)
    (fixed : Circuit.ReinitializedAt code environment
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ label)) :
    Circuit.ReinitializedAt code environment
      ((persistentCtx ctx width scalarWidth).quantumLayout.restrictSelectedBasis
        (persistentCtx ctx width scalarWidth).borrowedSelectionᶜ label) := by
  exact fixed

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

omit [Fact p.Prime] in
private lemma public_noBorrowedQuantum :
    (Recovery.PublicInput.context E (orderWidth problem)).borrowedQuantumWires = [] :=
  (Circuit.borrowedQuantumWires_preserved
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).trans rfl

omit [Fact p.Prime] in
private lemma terminal_noBorrowedQuantum :
    (Recovery.Layout.terminal p.size (orderWidth problem)).borrowedQuantumWires = [] := by
  have combined := public_noBorrowedQuantum E problem
  change ((Recovery.Layout.terminal p.size (orderWidth problem)).entries ++
    (Recovery.PublicInput.frame E (orderWidth problem)).entries).flatMap
      RuntimeEntry.borrowedQuantumWires = [] at combined
  rw [List.flatMap_append] at combined
  exact (List.append_eq_nil_iff.mp combined).1

/-- The literal selected public reset prepares the independently declared native physical label.
-/
lemma resetChild_reinitializedAt :
    Circuit.ReinitializedAt (resetChild E fieldTail problem seed) environment
      (sectionSeed E fieldTail problem seed) := by
  apply reinitialized_with_persistent_seed (resetChild E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    (publicResetLabel E fieldTail problem seed)
  let ctx := Recovery.Layout.terminal p.size (orderWidth problem)
  let raw := Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed
  let label := Recovery.Initialization.newResetLabel E fieldTail (orderWidth problem) seed
  let pureEnvironment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment :=
    ⟨environment.quantum, environment.classical⟩
  have fixed : Circuit.ReinitializedAt raw pureEnvironment
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ label) :=
    QuditShift.resetToBasis_reinitializedAt (allowAllocation := false)
      (Recovery.Initialization.newResetImplementations p.size (orderWidth problem))
      (Recovery.Initialization.newResetCells p (orderWidth problem)) label
      (terminal_noBorrowedQuantum E problem)
  have placed := EmbeddingRestart.reinitializedAt (environment := pureEnvironment)
    (allowAllocation := false)
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)) raw label fixed
      (terminal_noBorrowedQuantum E problem) (public_noBorrowedQuantum E problem) rfl
  exact BitWord.selectForCircuit_reinitializedAt (environment := environment) _ _ placed

/-- The same actual reset prepares the same seed beside all seven original retained cells. -/
lemma reset_reinitializedAt : Circuit.ReinitializedAt (reset E fieldTail problem seed) environment
    (sectionSeed E fieldTail problem seed) :=
  candidateCheck_sampleUnderPersistent_reinitializedAt (resetChild E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    (sectionSeed E fieldTail problem seed) (resetChild_reinitializedAt E fieldTail problem seed)
    (public_noBorrowedQuantum E problem)

/-- Every complete first-section record has the prescribed final owned seed. -/
lemma first_reinitializedAt (nontrivial : 2 ≤ problem.order) :
    Circuit.ReinitializedAt (first E fieldTail problem points seed r coefficient nontrivial)
      environment
      (sectionSeed E fieldTail problem seed) :=
  Circuit.RestartCleanup.afterAt
    ((reset E fieldTail problem seed).seq (body E problem points r coefficient nontrivial))
    (reset E fieldTail problem seed) environment (sectionSeed E fieldTail problem seed)
    (reset_reinitializedAt E fieldTail problem seed)

/-- The reused section has the same final seed without performing a new leading reset. -/
lemma reused_reinitializedAt (nontrivial : 2 ≤ problem.order) :
    Circuit.ReinitializedAt (reused E fieldTail problem points seed r coefficient nontrivial)
      environment
      (sectionSeed E fieldTail problem seed) :=
  Circuit.RestartCleanup.afterAt (body E problem points r coefficient nontrivial)
    (reset E fieldTail problem seed) environment (sectionSeed E fieldTail problem seed)
    (reset_reinitializedAt E fieldTail problem seed)

/-- The actual first read satisfies every nonempty output-state clause on every Reference input. -/
lemma first_problemStates (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} (input : OracleInput .empty (sectionCtx E problem) Reference) :
    ∀ requirement ∈ (firstProblem E fieldTail problem points seed nontrivial addends).states
      environment (),
      requirement.Holds input.caller
        ((firstRun E fieldTail problem points seed r coefficient nontrivial).finalState
          environment Reference input.state) := by
  intro requirement member
  change requirement ∈ [stateRequirement E fieldTail problem seed] at member
  simp only [List.mem_singleton] at member
  subst requirement
  exact Circuit.RestartCleanup.stateRequirement
    (firstRun E fieldTail problem points seed r coefficient nontrivial)
    environment (sectionSeed E fieldTail problem seed)
    (first_reinitializedAt E fieldTail problem points seed r coefficient nontrivial) input

/-- The reused read satisfies the identical fixed-seed output promise, with arbitrary Reference.
-/
lemma reused_problemStates (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register} (input : OracleInput .empty (sectionCtx E problem) Reference) :
    ∀ requirement ∈ (reusedProblem E fieldTail problem points seed nontrivial addends).states
      environment (),
      requirement.Holds input.caller
        ((reusedRun E fieldTail problem points seed r coefficient nontrivial).finalState
          environment Reference input.state) := by
  intro requirement member
  change requirement ∈ [stateRequirement E fieldTail problem seed] at member
  simp only [List.mem_singleton] at member
  subst requirement
  exact Circuit.RestartCleanup.stateRequirement
    (reusedRun E fieldTail problem points seed r coefficient nontrivial)
    environment (sectionSeed E fieldTail problem seed)
    (reused_reinitializedAt E fieldTail problem points seed r coefficient nontrivial) input

/-- Actual grouped first-section outputs establish the reused section's joint-seed condition. -/
lemma first_nextInput_seeded (nontrivial : 2 ≤ problem.order)
    {Reference : Register} (input : OracleInput .empty (sectionCtx E problem) Reference) :
    SeededInitialization E fieldTail problem seed
      (((first E fieldTail problem points seed r coefficient nontrivial).nextInput environment
        input).localState) :=
  Circuit.ReinitializedAt.nextInput_jointSeeded
    (first E fieldTail problem points seed r coefficient nontrivial)
    environment (sectionSeed E fieldTail problem seed)
    (first_reinitializedAt E fieldTail problem points seed r coefficient nontrivial) input

/-- The real next reset also supplies the joint seed after every reused section. -/
lemma reused_nextInput_seeded (nontrivial : 2 ≤ problem.order)
    {Reference : Register} (input : OracleInput .empty (sectionCtx E problem) Reference) :
    SeededInitialization E fieldTail problem seed
      (((reused E fieldTail problem points seed r coefficient nontrivial).nextInput environment
        input).localState) :=
  Circuit.ReinitializedAt.nextInput_jointSeeded
    (reused E fieldTail problem points seed r coefficient nontrivial)
    environment (sectionSeed E fieldTail problem seed)
    (reused_reinitializedAt E fieldTail problem points seed r coefficient nontrivial) input

/-- The initialized first section has the same nonempty final-state requirement. -/
lemma initialized_problemStates (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target)
    {Reference : Register}
    (input : OracleInput .empty (Recovery.PublicInput.frame E (orderWidth problem)) Reference) :
    ∀ requirement ∈ (initializedProblem E fieldTail problem points seed nontrivial addends).states
      environment (),
      requirement.Holds input.caller
        ((initializedAlgorithm E fieldTail problem points seed r coefficient
          nontrivial).run.finalState environment Reference input.state) := by
  intro requirement member
  change requirement ∈ [initializedStateRequirement E fieldTail problem seed] at member
  simp only [List.mem_singleton] at member
  subst requirement
  exact Circuit.RestartCleanup.stateRequirement
    (initializedAlgorithm E fieldTail problem points seed r coefficient nontrivial).run
    environment (sectionSeed E fieldTail problem seed)
    (Circuit.RestartCleanup.afterAt («prefix» E problem)
      (first E fieldTail problem points seed r coefficient nontrivial)
      environment (sectionSeed E fieldTail problem seed)
      (first_reinitializedAt E fieldTail problem points seed r coefficient nontrivial)) input

/-- The complete first-boundary certificate retains selection, all six execution fields,
the nonempty output seed promise and its independent native event allowance.
-/
lemma firstBoundary_certificate (nontrivial : 2 ≤ problem.order) (count : Nat)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    let setup := BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth
      problem))
    let allocation := retainPersistent (model := Model)
      (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    let terminal := packBatchResult (model := Model)
      (Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
    RetainsFirst (environment := environment) E problem (first E fieldTail problem points seed r
      coefficient nontrivial) ∧
    Nonempty (Circuit.OperationalEquiv
      (run E fieldTail problem points seed r coefficient nontrivial ((count + 1) + 1)).code
      (setup.seq ((allocation.seq
        ((first E fieldTail problem points seed r coefficient nontrivial).seq
          (Circuit.OperationalEquiv.rotatedTail (reset E fieldTail problem seed)
            (body E problem points r coefficient nontrivial) count))).seq terminal))) ∧
    (∀ (Reference : Register) (input : OracleInput .empty (sectionCtx E problem) Reference),
      ∀ requirement ∈ (firstProblem E fieldTail problem points seed nontrivial addends).states
        environment (),
        requirement.Holds input.caller
          ((firstRun E fieldTail problem points seed r coefficient nontrivial).finalState
            environment Reference input.state)) ∧
    (∀ path, (first E fieldTail problem points seed r coefficient nontrivial).resourcePool path ≤
      sectionBudget E problem nontrivial) :=
  ⟨first_retainsFirst E fieldTail problem points seed r coefficient nontrivial,
    ⟨run_firstBoundary E fieldTail problem points seed r coefficient nontrivial count⟩,
    fun _ input => first_problemStates E fieldTail problem points seed r coefficient
      nontrivial addends input,
    first_pool_le E fieldTail problem points seed r coefficient nontrivial⟩

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
