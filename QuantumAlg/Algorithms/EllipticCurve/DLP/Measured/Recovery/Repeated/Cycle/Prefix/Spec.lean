/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Domain
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Resources

/-!
# Independent first ECC cycle from the original caller

The first cycle includes one-time initialization, the seven-cell allocation,
one complete checked sample and the following physical reset. The caller
supplies only the original public points and an arbitrary normalized joint
state. The retained bank is allocated internally, with no caller latch or
quantum seed assumption.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ScalarMultiplication.MeasuredPlacement
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private abbrev sectionCtx : RuntimeCtx .quantum :=
  persistentCtx (PublicInput.terminal E (orderWidth problem))
    (Canonical.Layout.fieldWidth E) (orderWidth problem)

/-- A present, bounded scalar satisfying the original public group equation. -/
def initializedFirstCheckedSectionAccepts :
    CShape.Value (.product .bit (.unsignedWord (orderWidth problem))) → Prop
  | .product flag word =>
    flag.toBool = true ∧ word.toNat < problem.order ∧
      word.toNat • problem.generator.toMathlib = problem.target.toMathlib

/-- The independent one-time native initialization allowance is charged
alongside the same complete checked-section envelope. -/
def initializedFirstCheckedSectionEventBudget :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model) :=
  BitWord.liftQuantumPool
      (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))) +
    checkedSectionEventBudget E problem nontrivial

/-- The first cycle's prescribed owned seed is observed on the complete
original-caller output, with arbitrary external-reference correlations. -/
def initializedFirstCheckedSectionStateRequirement :
    StateRequirement (PublicInput.before E (orderWidth problem)) (sectionCtx E problem) :=
  .marginal _ (checkedSectionRead E problem) (fun _ _ =>
    StatePromise.pure (NormalizedVector.ket
      (checkedSectionSeed E fieldTail sameWidth fits problem seed)))

/-- One complete checked sample from the original admitted caller.

**Input.**
- The original two public points, with arbitrary normalized owned quantum
  state and external reference; no caller-owned retained bank or seed is assumed.
**Output.**
- The actual accepted bit and selected scalar, followed by the fixed physical
  reset seed. A present result is bounded and solves the public group equation.
**Resource budget.**
- One-time native initialization plus the common complete checked-section
  envelope; one allocated seven-cell bank and reused recovery scratch.
**Success.**
- The original corrected one-attempt floor, truncated to a probability threshold.
**Source.**
- [PZ03, ecc.tex:448-556] for the measured group-shift computation; the
  corrected floor and native envelopes are derived in the generic owners.
-/
def initializedFirstCheckedSectionProblem
    (_addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : Problem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (PublicInput.before E (orderWidth problem)) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  valid := PublicInput.inputDomain E (orderWidth problem) problem
  initialization := fun _ => True
  accepts := fun _ value => initializedFirstCheckedSectionAccepts E problem value
  successLB := checkedSectionSuccessLB E problem points seed
  states := [initializedFirstCheckedSectionStateRequirement E fieldTail sameWidth fits
    problem seed]
  resources :=
    { events := initializedFirstCheckedSectionEventBudget E problem nontrivial
      resident := (checkedSectionResourceBudget E problem nontrivial).resident
      auxiliary := (checkedSectionResourceBudget E problem nontrivial).auxiliary }
  depth :=
    { duration := fun _ => 1
      limit := ResourcePool.weightedCount (fun _ => 1)
        (initializedFirstCheckedSectionEventBudget E problem nontrivial)
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
