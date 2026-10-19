/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.Resources

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Admission
import all QuantumAlg.Core.Execution.Restart.Admission

/-!
# Independent first and reused native checked-section contracts

The corrected floor, accepted-word equation, exact retention of an earlier
accepted word, full borrowed obligation and fixed owned output seed are
unchanged in mathematical form. The physical carrier and prescribed seed
are explicitly reconstructed from the reduced public placement.

The first section admits arbitrary normalized owned states and References.
The reused section alone requires JointSeededInitialization. The initialized
first section starts from the original public-point domain with no caller
latch or seed assumption, and pays the real one-time preparation budget.

State promises, borrowed restoration and resource inequalities have separate
Boundary proof owners for the first and reused carriers defined here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP Canonical.Probability
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The physical native reset label in public coordinates; the classical frame has no wires. -/
def publicResetLabel : (Recovery.PublicInput.context E (orderWidth problem)).register.Index :=
  let placement := Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)
  placement.basis.symm
    (Recovery.Initialization.newResetLabel E fieldTail (orderWidth problem) seed,
      placement.frame.quantumLayout.zeroLabel)

/-- The independently prescribed owned seed beside the same seven zero-wire cells. -/
def sectionSeed : (sectionCtx E problem).quantumLayout.SelectedBasis
    (sectionCtx E problem).borrowedSelectionᶜ :=
  (sectionCtx E problem).quantumLayout.restrictSelectedBasis
    (sectionCtx E problem).borrowedSelectionᶜ (publicResetLabel E fieldTail problem seed)

/-- Only a reused section requires the already prepared joint local seed. -/
def SeededInitialization
    (state : ExecutionState (Store (sectionCtx E problem) × Model.HiddenState)
      (sectionCtx E problem).register) : Prop :=
  Circuit.JointSeededInitialization (model := Model) (sectionCtx E problem)
    (sectionSeed E fieldTail problem seed) state

/-- The same accepted bit, scalar bound, group equation and first-value retention condition. -/
def accepts (before : Store (sectionCtx E problem)) :
    CShape.Value (.product .bit (.unsignedWord (orderWidth problem))) → Prop
  | .product flag word =>
    flag.toBool = true ∧ word.toNat < problem.order ∧
      word.toNat • problem.generator.toMathlib = problem.target.toMathlib ∧
      ((before.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
        word = before.read (.storage (persistentSelected _ _ _).toCStorageRef))

/-- The original one-attempt floor, with the same exceptional term and no positivity premise. -/
def successLB : ProbabilityLowerBound where
  value := 1 - ENNReal.ofReal (1 - ((problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)))
  le_one := tsub_le_self

/-- The actual pair read must observe the fixed physical owned seed at section output. -/
def stateRequirement : StateRequirement (sectionCtx E problem) (sectionCtx E problem) :=
  .marginal _ (read E problem)
    (fun _ _ => StatePromise.pure (NormalizedVector.ket (sectionSeed E fieldTail problem seed)))

/-- The original arbitrary-state first-section protocol on the explicit native carrier. -/
def firstProblem (nontrivial : 2 ≤ problem.order)
    (_addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Problem Model (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) where
  Witness := Unit
  valid := fun _ _ => InputDomain E problem
  initialization := fun _ _ _ => True
  accepts := fun _ _ => accepts E problem
  successLB := fun _ _ => successLB E problem points seed
  states := fun _ _ => [stateRequirement E fieldTail problem seed]
  resources := sectionResources E problem nontrivial
  quantumTimeLimit := sectionTimeLimit E problem nontrivial

/-- The reused protocol differs only in requiring the predecessor's joint seed. -/
def reusedProblem (nontrivial : 2 ≤ problem.order)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Problem Model (sectionCtx E problem) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) :=
  { firstProblem E fieldTail problem points seed nontrivial addends with
    initialization := fun _ _ => SeededInitialization E fieldTail problem seed }

/-- Initialized first-cycle acceptance has no preexisting retained-selection condition. -/
def initializedAccepts :
    CShape.Value (.product .bit (.unsignedWord (orderWidth problem))) → Prop
  | .product flag word =>
    flag.toBool = true ∧ word.toNat < problem.order ∧
      word.toNat • problem.generator.toMathlib = problem.target.toMathlib

/-- Original allocation and actual first-section events are paid once, before any reuse. -/
def initializedBudget (nontrivial : 2 ≤ problem.order) : ResourcePool Model :=
  BitWord.liftQuantumPool (Recovery.PublicInput.Allocation.Events.allocationBudget p.size) +
    sectionBudget E problem nontrivial

/-- The fixed owned seed is also required when observing the complete original-caller output. -/
def initializedStateRequirement :
    StateRequirement (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E problem) :=
  .marginal _ (read E problem)
    (fun _ _ => StatePromise.pure (NormalizedVector.ket (sectionSeed E fieldTail problem seed)))

/-- One complete initialized first section with the same domain, output promise and success floor.
-/
def initializedProblem (nontrivial : 2 ≤ problem.order)
    (_addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Problem Model (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) where
  Witness := Unit
  valid := fun _ _ => Recovery.PublicInput.Support.inputDomain E (orderWidth problem) problem
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ value => initializedAccepts E problem value
  successLB := fun _ _ => successLB E problem points seed
  states := fun _ _ => [initializedStateRequirement E fieldTail problem seed]
  resources :=
    { events := initializedBudget E problem nontrivial
      resident := (sectionResources E problem nontrivial).resident
      auxiliary := (sectionResources E problem nontrivial).auxiliary }
  quantumTimeLimit := ResourcePool.weightedCount (fun _ => 1)
    (initializedBudget E problem nontrivial)

/-- No final option pack is added to this actual first-boundary read. -/
def initializedAlgorithm (r : Nat) (coefficient : (ZMod p)ˣ) (nontrivial : 2 ≤ problem.order) :
    Algorithm Model (Recovery.PublicInput.frame E (orderWidth problem)) (sectionCtx E problem)
      (.product .bit (.unsignedWord (orderWidth problem))) where
  run := ⟨(«prefix» E problem).seq
    (first E fieldTail problem points seed r coefficient nontrivial),
      Output.all _ (read E problem)⟩

/-- The main native problem admits exactly the same original callers into the first-cycle problem.
-/
lemma algorithm_admits_initializedFirstCycle (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth (ECDLP.Canonical.problem I))
        (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target)
    (count : Nat) (failure : ℝ) {Reference : Register}
    (input : OracleInput .empty (Spec.inputContext E I) Reference)
    (admitted : (QuantumAlg.EllipticCurve.LogicalResources.problem E I count failure).Admits
      environment ()
      input) :
    (initializedProblem E fieldTail (ECDLP.Canonical.problem I) points seed
      I.subgroupOrder_prime.two_le addends).Admits environment () input :=
  ⟨admitted.1, True.intro⟩

/-- The real prefix establishes full first-section admission from the original native caller. -/
lemma algorithm_prefix_admits_checkedSection (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E)
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth (ECDLP.Canonical.problem I))
        (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target)
    (count : Nat) (failure : ℝ) {Reference : Register}
    (input : OracleInput .empty (Spec.inputContext E I) Reference)
    (admitted : (QuantumAlg.EllipticCurve.LogicalResources.problem E I count failure).Admits
      environment ()
      input) :
    (firstProblem E fieldTail (ECDLP.Canonical.problem I) points seed
      I.subgroupOrder_prime.two_le addends).Admits environment ()
        ((«prefix» E (ECDLP.Canonical.problem I)).nextInput environment input) :=
  ⟨algorithm_prefix_domain E I count failure input admitted, True.intro⟩

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
