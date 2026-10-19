/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Frames

/-!
# Actual first-phase LLL invariant preservation

The represented Gram entries determine the actual rounded first quotient.
The stored Lovasz result drives the original phase update, and the final Gram
refresh supplies the invariant for the next actual iteration.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original invariant supplies exactly the actual first-pair input readings. -/
lemma first_initial (refs : Refs ctx width) (input : NumberTheory.IntegerBasis3)
    (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    LatticeFirstPairMachine.Initial refs.first store state.basis := by
  have norm := invariant.gram .g11
  change RawSignedRepresents (store.read (.storage refs.metric.g11.toCStorageRef))
    (NumberTheory.integerPointDot state.basis.first state.basis.first) at norm
  rw [NumberTheory.integerPointDot_self] at norm
  constructor
  · rw [refs.firstBasis]
    exact invariant.basis
  · rw [refs.first.numerator, refs.firstMetric]
    exact rawSignedRepresents_decode_eq _ _ invariant.stepFits.widthPos
      (invariant.gram .g21) invariant.stepFits.firstDotRange
  · rw [refs.first.denominator, refs.firstMetric]
    exact rawSignedRepresents_toNat_eq_of_lt _ norm invariant.stepFits.firstNormFits

/-- Full rank and the original scalar range obligations satisfy the first-pair numeric domain. -/
lemma first_fits (refs : Refs ctx width) (input : NumberTheory.IntegerBasis3)
    (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    LatticeFirstPairMachine.Fits width state.basis :=
  ⟨invariant.stepFits.widthPos,
    Nat.pos_of_ne_zero invariant.bounded.fullRank.firstSquaredNorm_ne_zero,
    invariant.stepFits.firstNormFits, invariant.stepFits.firstReducedSecondFits⟩

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual first-pair writes preserve both original phase bits. -/
lemma first_pair_phase (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (phase : NumberTheory.LLLPhase3)
    (rep : refs.machine.PhaseRepresents store phase) :
    refs.machine.PhaseRepresents
      (LatticeFirstPairMachine.firstPairStep (model := model) refs.first store).1 phase :=
  phase_of_frames refs phase
    (LatticeFirstPairMachine.firstPairInto_callerFrame (model := model) refs.first store _
      (fun cell _ => separation.secondPhaseFirst cell))
    (LatticeFirstPairMachine.firstPairInto_callerFrame (model := model) refs.first store _
      (fun cell _ => separation.doneFirst cell)) rep

/-- The actual stored first Lovasz result updates its phase while preserving the selected basis. -/
lemma first_advance_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (passes : Bool)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (phase : refs.machine.PhaseRepresents store .first)
    (decision : (store.read (.storage refs.first.lovasz.passes.toCStorageRef)).toBool = passes) :
    LatticeMetricMachine.BasisRawRepresents
      (firstAdvanceStep (model := model) refs store).1 refs.machine.basis basis ∧
      refs.machine.PhaseRepresents (firstAdvanceStep (model := model) refs store).1
        (if passes then .second else .first) := by
  change LatticeMetricMachine.BasisRawRepresents
    (firstAdvanceArmStep (model := model) refs
      (store.read (.storage refs.first.lovasz.passes.toCStorageRef)) store).1
    refs.machine.basis basis ∧ refs.machine.PhaseRepresents
      (firstAdvanceArmStep (model := model) refs
        (store.read (.storage refs.first.lovasz.passes.toCStorageRef)) store).1
      (if passes then .second else .first)
  cases observed : store.read (.storage refs.first.lovasz.passes.toCStorageRef) with
  | bit flag =>
    have equal : flag = passes := by simpa only [observed, CShape.Value.toBool] using decision
    rw [← equal]
    cases flag
    · exact ⟨rep, phase⟩
    · exact ⟨transition_basis refs separation .firstPass store basis rep,
        LatticePhaseControl.transitionInto_correct refs.machine separation.machine .firstPass
          store phase⟩

/-- The complete actual first driver arm preserves the original mathematical LLL invariant. -/
lemma firstStepInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (input : NumberTheory.IntegerBasis3) (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) (phase : state.phase = .first) :
    StoreInvariant refs input (firstStep (model := model) refs store).1
      (NumberTheory.lllStep3 state) := by
  have pair := LatticeFirstPairMachine.firstPairInto_correct (model := model)
    refs.first separation.first store
    state.basis (first_initial refs input store state invariant)
    (first_fits refs input store state invariant)
  have represented := pair.basisRep
  rw [refs.firstBasis] at represented
  have phaseBefore : refs.machine.PhaseRepresents store .first := by
    rw [← phase]
    exact invariant.phase
  have advanced := first_advance_correct refs separation _ _ _ represented
    (first_pair_phase refs separation store .first phaseBefore) pair.passes
  have refreshed := LatticeMetricMachine.refreshInto_correct refs.machine.basis refs.metric
    separation.metric _ _ advanced.1
  have phaseAfter := refresh_phase refs separation _ _ advanced.2
  have mathematical := NumberTheory.lllStep3_first_basis_phase state phase
  refine ⟨?_, ?_, ?_, invariant.bounded.step, invariant.capacity,
    LatticeStepBounds.stepFits_of_boundedFrom invariant.bounded.step invariant.capacity⟩
  · rw [mathematical.1]
    exact refreshed.2
  · rw [mathematical.2]
    exact phaseAfter
  · rw [mathematical.1]
    exact refreshed.1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
