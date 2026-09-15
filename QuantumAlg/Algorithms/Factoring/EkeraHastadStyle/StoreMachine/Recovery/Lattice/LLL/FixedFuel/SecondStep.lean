/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.FirstStep

/-!
# Actual second-phase LLL invariant preservation

The original Gram invariant and full-rank range bounds supply both actual
rounded quotients and area tests. The actual stored comparison selects finish
or restart, and the final Gram refresh restores the next iteration's invariant.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original invariant supplies the complete actual second-pair initial representation. -/
theorem second_initial (refs : Refs ctx width) (input : NumberTheory.IntegerBasis3)
    (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    LatticeSecondPairFullMachine.Initial refs.second store state.basis := by
  constructor
  · rw [refs.secondBasis]
    exact invariant.basis
  · rw [refs.secondMetric]
    have norm := invariant.gram .g11
    change RawSignedRepresents (store.read (.storage refs.metric.g11.toCStorageRef))
      (NumberTheory.integerPointDot state.basis.first state.basis.first) at norm
    rw [NumberTheory.integerPointDot_self] at norm
    exact norm
  · rw [refs.secondMetric]
    exact invariant.gram .g31
  · rw [refs.secondMetric]
    have norm := invariant.gram .g22
    change RawSignedRepresents (store.read (.storage refs.metric.g22.toCStorageRef))
      (NumberTheory.integerPointDot state.basis.second state.basis.second) at norm
    rw [NumberTheory.integerPointDot_self] at norm
    exact norm

/-- Full rank and the original seven scalar bounds satisfy every actual second-pair phase. -/
theorem second_fits (refs : Refs ctx width) (input : NumberTheory.IntegerBasis3)
    (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) :
    LatticeSecondPairFullMachine.Fits width state.basis := by
  have denominatorPositive : 0 < state.basis.secondReductionDenominator := by
    have nonzero := invariant.bounded.fullRank.secondReductionDenominator_ne_zero
    have nonnegative : 0 ≤ state.basis.secondReductionDenominator := by
      simp [NumberTheory.IntegerBasis3.secondReductionDenominator]
    omega
  have firstPositive : 0 < NumberTheory.integerPointSquaredNorm state.basis.first :=
    Nat.pos_of_ne_zero invariant.bounded.fullRank.firstSquaredNorm_ne_zero
  refine ⟨⟨invariant.stepFits.widthPos, invariant.stepFits.secondNumeratorRange,
    denominatorPositive, ?_⟩,
    ⟨invariant.stepFits.widthPos, firstPositive, invariant.stepFits.firstNormFits,
      invariant.stepFits.postSecondDotRange⟩,
    ⟨invariant.stepFits.area12Fits, invariant.stepFits.secondReducedArea13Fits⟩⟩
  change (NumberTheory.integerPointAreaSquared state.basis.first state.basis.second : Int) <
    (CShape.wordModulus width : Nat)
  exact_mod_cast invariant.stepFits.area12Fits

/-- The actual second-pair writes preserve both original phase bits. -/
theorem second_pair_phase (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (phase : NumberTheory.LLLPhase3)
    (rep : refs.machine.PhaseRepresents store phase) :
    refs.machine.PhaseRepresents
      (LatticeSecondPairFullMachine.secondPairStep refs.second store).1 phase :=
  phase_of_frames refs phase
    (LatticeSecondPairFullMachine.secondPairInto_callerFrame refs.second store _
      (fun cell _ => separation.secondPhaseSecond cell))
    (LatticeSecondPairFullMachine.secondPairInto_callerFrame refs.second store _
      (fun cell _ => separation.doneSecond cell)) rep

/-- The second Lovasz result selects finish or restart without changing its selected basis. -/
theorem second_advance_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (passes : Bool)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (phase : refs.machine.PhaseRepresents store .second)
    (decision :
      (store.read (.storage refs.second.branch.lovasz.passes.toCStorageRef)).toBool = passes) :
    LatticeMetricMachine.BasisRawRepresents (secondAdvanceStep refs store).1 refs.machine.basis
      basis ∧
      refs.machine.PhaseRepresents (secondAdvanceStep refs store).1
        (if passes then .done else .first) := by
  change LatticeMetricMachine.BasisRawRepresents
    (secondAdvanceArmStep refs
      (store.read (.storage refs.second.branch.lovasz.passes.toCStorageRef)) store).1
    refs.machine.basis basis ∧ refs.machine.PhaseRepresents
      (secondAdvanceArmStep refs
        (store.read (.storage refs.second.branch.lovasz.passes.toCStorageRef)) store).1
      (if passes then .done else .first)
  cases observed : store.read (.storage refs.second.branch.lovasz.passes.toCStorageRef) with
  | bit flag =>
    have equal : flag = passes := by simpa only [observed, CShape.Value.toBool] using decision
    rw [← equal]
    cases flag
    · exact ⟨transition_basis refs separation .secondFail store basis rep,
        LatticePhaseControl.transitionInto_correct refs.machine separation.machine .secondFail
          store phase⟩
    · exact ⟨transition_basis refs separation .secondPass store basis rep,
        LatticePhaseControl.transitionInto_correct refs.machine separation.machine .secondPass
          store phase⟩

/-- The actual complete second driver arm preserves the original mathematical LLL invariant. -/
theorem secondStepInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (input : NumberTheory.IntegerBasis3) (store : Store ctx) (state : NumberTheory.LLLState3)
    (invariant : StoreInvariant refs input store state) (phase : state.phase = .second) :
    StoreInvariant refs input (secondStep refs store).1 (NumberTheory.lllStep3 state) := by
  have pair := LatticeSecondPairFullMachine.secondPairInto_correct refs.second separation.second
    store
    state.basis (second_initial refs input store state invariant)
    (second_fits refs input store state invariant)
  have represented := pair.basisRep
  rw [refs.secondBasis] at represented
  have phaseBefore : refs.machine.PhaseRepresents store .second := by
    rw [← phase]
    exact invariant.phase
  have advanced := second_advance_correct refs separation _ _ _ represented
    (second_pair_phase refs separation store .second phaseBefore) pair.passes
  have refreshed := LatticeMetricMachine.refreshInto_correct refs.machine.basis refs.metric
    separation.metric _ _ advanced.1
  have phaseAfter := refresh_phase refs separation _ _ advanced.2
  have mathematical := NumberTheory.lllStep3_second_basis_phase state phase
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
