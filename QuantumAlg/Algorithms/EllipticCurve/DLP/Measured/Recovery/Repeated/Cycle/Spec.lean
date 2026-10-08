/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.RoundResources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Selected
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.TailResources
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Admission

/-!
# Independent protocol for one completed checked ECC section

The caller fixes the public points, selected-word invariant, structural
accepted/selected output, success threshold, final owned-bank seed and native
resource allowances before checking either physical section. The first section
resets an arbitrary incoming quantum state. A reused section starts after the
preceding physical reset and therefore requires that independently stated seed
at its input; predecessor-to-successor admission remains a separate proof.
The success threshold uses the original corrected candidate floor and can be
zero when that floor is not positive; the original finite-repetition calibration
remains separate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP ClassicalRoutines.EllipticCurve
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

/-- The original reset label on the unchanged quantum layout beside seven
persistent classical cells. The value is fixed by the public parameters. -/
def checkedSectionSeed :
    (sectionCtx E problem).quantumLayout.SelectedBasis
      (sectionCtx E problem).borrowedSelectionᶜ :=
  (PublicInput.terminal E (orderWidth problem)).quantumLayout.restrictSelectedBasis
    (PublicInput.terminal E (orderWidth problem)).borrowedSelectionᶜ
    (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed)

/-- The same public sampling seed on all physical wires, before restricting
to the owned selection used by output-state promises. -/
def checkedSectionAllSeed :
    (sectionCtx E problem).quantumLayout.SelectedBasis Finset.univ :=
  (sectionCtx E problem).quantumLayout.restrictSelectedBasis Finset.univ
    (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed)

/-- A reused section starts only from the fixed seed established by the
preceding real reset. Every supported classical/service block has a joint
extension witnessing the same owned seed; with no borrowed wires,
`JointSeededInitialization.allSeed` gives the full local seed. The public
point and selected-word conditions remain in the separate classical domain. -/
def checkedSectionSeededInitialization
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ)
    (problem : KnownOrderProblem E.GroupPoint) (seed : AffinePoint E)
    (state : ExecutionState
      (Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState)
      (sectionCtx E problem).register) : Prop :=
  Circuit.JointSeededInitialization
    (model := .quantum AlgorithmGate.model .empty BitWord.model) (sectionCtx E problem)
    (checkedSectionSeed E fieldTail sameWidth fits problem seed) state

omit [Fact p.Prime] in
private theorem checkedSection_allOwned :
    (sectionCtx E problem).borrowedSelectionᶜ = Finset.univ := by
  have none : (sectionCtx E problem).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  simp [RuntimeCtx.borrowedSelection, none]

private theorem restrictSeed_all {count : Nat} (layout : QuantumLayout count)
    (selection : Finset (Fin count)) (all : selection = Finset.univ)
    (basis : layout.Basis) :
    all ▸ layout.restrictSelectedBasis selection basis =
      layout.restrictSelectedBasis Finset.univ basis := by
  cases all
  rfl

/-- The real joint-state input condition entails the prescribed pure seed
on every physical wire of the reused ECC section. -/
theorem checkedSectionSeededInitialization_fullSeed
    (state : ExecutionState
      (Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState)
      (sectionCtx E problem).register)
    (seeded : checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed state)
    (entry : Store (sectionCtx E problem) × ClassicalOracleModel.empty.HiddenState) :
    (StatePromise.pure (NormalizedVector.ket
      (checkedSectionAllSeed E fieldTail sameWidth fits problem seed))).Holds
      ((state.block entry).reindex
        (S := (sectionCtx E problem).quantumLayout.selectedRegister Finset.univ)
        (sectionCtx E problem).quantumLayout.allSelectedBasisEquiv) := by
  have all := checkedSection_allOwned E problem
  have pure := Circuit.JointSeededInitialization.allSeed
    (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (checkedSectionSeed E fieldTail sameWidth fits problem seed)
    all state seeded entry
  have sameSeed : (all ▸ checkedSectionSeed E fieldTail sameWidth fits problem seed) =
      checkedSectionAllSeed E fieldTail sameWidth fits problem seed := by
    exact restrictSeed_all _ _ all _
  rw [sameSeed] at pure
  exact pure

/-- Read the two original live latches as an unallocated optional scalar:
the first bit is presence, and the second word is its stored payload. -/
def checkedSectionRead : OutputRead (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) :=
  .read (.product
    (.storage (persistentAccepted _ _ _).toCStorageRef)
    (.storage (persistentSelected _ _ _).toCStorageRef))

/-- The owned-bank seed is the original reset label. It is fixed before
the input, path and readout, independently of either section implementation. -/
def checkedSectionStateRequirement {shape : CShape}
    (read : OutputRead (sectionCtx E problem) shape) :
    StateRequirement (sectionCtx E problem) (sectionCtx E problem) :=
  .marginal _ read (fun _ _ => StatePromise.pure (NormalizedVector.ket
    (checkedSectionSeed E fieldTail sameWidth fits problem seed)))

/-- The admitted local state fixes only the two public point interpretations
and the previously selected scalar invariant on supported classical blocks. -/
def checkedSectionInputDomain
    (localState : ExecutionState (Store (sectionCtx E problem))
      (sectionCtx E problem).register) : Prop :=
  ∀ store, 0 < (localState.block store).mass →
    PointRepresents (Canonical.Layout.curveSpec E)
      (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
    PointRepresents (Canonical.Layout.curveSpec E)
      (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
        (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib ∧
    (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat < problem.order ∧
    ((store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
      (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
        problem.generator.toMathlib = problem.target.toMathlib)

/-- Acceptance means that the checked optional scalar is present, bounded and
solves the public equation; any previously accepted word is retained exactly. -/
def checkedSectionAccepts
    (before : Store (sectionCtx E problem)) :
    CShape.Value (.product .bit (.unsignedWord (orderWidth problem))) → Prop
  | .product flag word =>
    flag.toBool = true ∧ word.toNat < problem.order ∧
      word.toNat • problem.generator.toMathlib = problem.target.toMathlib ∧
      ((before.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
        word = before.read (.storage (persistentSelected _ _ _).toCStorageRef))

/-- The source-derived corrected one-attempt floor, truncated to a valid
probability threshold without an unsupported positivity assumption. -/
def checkedSectionSuccessLB : ProbabilityLowerBound where
  value := 1 - ENNReal.ofReal (1 - ((problem.order : ℝ) * Nat.totient problem.order /
    (4 * (fourierModulus problem : ℝ) ^ 2) -
      4 * Real.sqrt (preparedExceptionalMass problem points seed)))
  le_one := tsub_le_self

/-- Independent complete-section native allowance: original reset/sample,
all checked recovery operations, and the next physical reset. The reused
section may use less than this common first/reused envelope. -/
def checkedSectionEventBudget :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model) :=
  BitWord.liftQuantumPool (samplingRoundBudget E problem) +
    attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) +
    BitWord.liftQuantumPool (samplingResetBudget E (orderWidth problem))

/-- A one-time seven-cell bank and the maximum successive recovery scratch
scope, without multiplying live storage by the number of attempts. -/
def checkedSectionResourceBudget :
    ResourceBudget (.quantum AlgorithmGate.model .empty BitWord.model) where
  events := checkedSectionEventBudget E problem nontrivial
  resident := recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E)
      (orderWidth problem) +
    persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
    (PublicInput.terminal E (orderWidth problem)).residentSpace
  auxiliary := recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E)
      (orderWidth problem) +
    persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
    (PublicInput.terminal E (orderWidth problem)).auxiliarySpace

/-- The first completed checked attempt with a real optional-scalar read and fixed
post-reset state, specified independently of the first or reused circuit.
The public addend table must encode the two stated group points; this is a
source-level parameter condition, never an extra constraint on local states.

**Input.**
- A correctly encoded public addend table, the original two borrowed public
  points and a bounded, sound retained selection; all normalized quantum states
  and external references are allowed because this section starts with a reset.
**Output.**
- The original accepted bit and selected word, interpreted as an optional
  scalar. An accepted word is bounded, solves the public group equation, and
  preserves an earlier accepted value exactly.
**Resource budget.**
- One complete native reset/sample, checked recovery and following reset;
  one persistent seven-cell bank and successive recovery scratch, with unit
  whole-section depth bounded by the same independent native envelope.
**Success.**
- At least the corrected one-attempt candidate floor when positive, zero
  otherwise; finite-repetition calibration is stated separately.
**Source.**
- [PZ03, ecc.tex:448-556] for the measured group-shift construction; the
  fixed native bounds and corrected sampling floor are derived from the
  registered implementation and finite-cyclic DLP analysis.
-/
def checkedSectionProblem
    (_addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : Problem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) where
  valid := checkedSectionInputDomain E problem
  initialization := fun _ => True
  accepts := checkedSectionAccepts E problem
  successLB := checkedSectionSuccessLB E problem points seed
  states := [checkedSectionStateRequirement E fieldTail sameWidth fits problem seed
    (checkedSectionRead E problem)]
  resources := checkedSectionResourceBudget E problem nontrivial
  depth :=
    { duration := fun _ => 1
      limit := ResourcePool.weightedCount (fun _ => 1)
        (checkedSectionEventBudget E problem nontrivial)
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- The reused readout/check/reset section has the same independent output,
success and resource contract as the first section, but its input quantum
bank must already have the public seed. This is a predecessor admission
condition, not an assertion that the reused circuit performs another reset. -/
def reusedCheckedSectionProblem
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) : Problem
    (.quantum AlgorithmGate.model .empty BitWord.model)
    (sectionCtx E problem) (sectionCtx E problem)
    (.product .bit (.unsignedWord (orderWidth problem))) :=
  { checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial addends with
    initialization := checkedSectionSeededInitialization E fieldTail sameWidth fits problem seed }

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
