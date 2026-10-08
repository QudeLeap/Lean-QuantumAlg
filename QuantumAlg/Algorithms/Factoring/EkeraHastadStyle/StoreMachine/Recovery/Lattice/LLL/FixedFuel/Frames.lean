/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Program.Execution

/-!
# Actual fixed-fuel caller and phase frames

The original caller separation excludes all pair cells and both phase bits.
Every actual selected arm and iteration retains those reads. Phase writes keep
the represented basis, and pair and Gram writes keep the actual phase bits.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original caller frame excludes every pair identity and both driver latch writes. -/
structure CallerSeparated (refs : Refs ctx width) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  first : ∀ cell, LatticeFirstPairMachine.cellKey refs.first cell ∉ other.storageKeys
  second : ∀ cell, LatticeSecondPairFullMachine.cellKey refs.second cell ∉ other.storageKeys
  secondPhase : refs.machine.secondPhase.key ∉ other.storageKeys
  done : refs.machine.done.key ∉ other.storageKeys

/-- The original phase encoding depends only on its two actual bit readings. -/
theorem phase_of_frames (refs : Refs ctx width) {before after : Store ctx}
    (phase : NumberTheory.LLLPhase3)
    (secondFrame : after.read (phaseInput refs.machine.secondPhase) =
      before.read (phaseInput refs.machine.secondPhase))
    (doneFrame : after.read (phaseInput refs.machine.done) =
      before.read (phaseInput refs.machine.done))
    (rep : refs.machine.PhaseRepresents before phase) :
    refs.machine.PhaseRepresents after phase := by
  cases phase <;> simp only [LatticeState.MachineRefs.PhaseRepresents] at rep ⊢
  all_goals
    constructor
    · change (after.read (phaseInput refs.machine.secondPhase)).toBool = _
      rw [secondFrame]
      exact rep.1
    · change (after.read (phaseInput refs.machine.done)).toBool = _
      rw [doneFrame]
      exact rep.2

/-- The represented basis depends only on its nine actual named coordinate readings. -/
theorem basis_of_frames (refs : Refs ctx width) {before after : Store ctx}
    (basis : NumberTheory.IntegerBasis3)
    (reads : ∀ cell, after.read (LatticeMetricMachine.basisCellInput refs.machine.basis cell) =
      before.read (LatticeMetricMachine.basisCellInput refs.machine.basis cell))
    (rep : LatticeMetricMachine.BasisRawRepresents before refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents after refs.machine.basis basis := by
  intro row
  cases row with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstFirst))
        basis.first.1
      rw [reads]
      exact (rep .first).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstSecond))
        basis.first.2.1
      rw [reads]
      exact (rep .first).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstThird))
        basis.first.2.2
      rw [reads]
      exact (rep .first).2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondFirst))
        basis.second.1
      rw [reads]
      exact (rep .second).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondSecond))
        basis.second.2.1
      rw [reads]
      exact (rep .second).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondThird))
        basis.second.2.2
      rw [reads]
      exact (rep .second).2.2
  | third =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdFirst))
        basis.third.1
      rw [reads]
      exact (rep .third).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdSecond))
        basis.third.2.1
      rw [reads]
      exact (rep .third).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdThird))
        basis.third.2.2
      rw [reads]
      exact (rep .third).2.2

/-- Embed a basis coordinate into the original basis-and-phase allocation. -/
def basisMachineCell : LatticeMetricMachine.BasisCell → LatticeState.MachineCell
  | .firstFirst => .firstFirst
  | .firstSecond => .firstSecond
  | .firstThird => .firstThird
  | .secondFirst => .secondFirst
  | .secondSecond => .secondSecond
  | .secondThird => .secondThird
  | .thirdFirst => .thirdFirst
  | .thirdSecond => .thirdSecond
  | .thirdThird => .thirdThird

/-- The original machine identity of the selected phase latch. -/
abbrev phaseMachineCell : LatticePhaseControl.Transition → LatticeState.MachineCell
  | .firstPass | .secondFail => .secondPhase
  | .secondPass => .done

/-- Original machine separation keeps every phase write outside every basis coordinate. -/
theorem phase_avoids_basis (refs : Refs ctx width) (separation : Separation refs)
    (transition : LatticePhaseControl.Transition) (cell : LatticeMetricMachine.BasisCell) :
    (LatticePhaseControl.writtenRef refs.machine transition).key ∉
      (LatticeMetricMachine.basisCellInput refs.machine.basis cell).storageKeys := by
  have different : phaseMachineCell transition ≠ basisMachineCell cell := by
    cases transition <;> cases cell <;> decide
  have keyNe : refs.machine.keyOf (phaseMachineCell transition) ≠
      refs.machine.keyOf (basisMachineCell cell) := fun equal => different (separation.machine
        equal)
  cases transition <;> cases cell <;>
    simpa only [LatticePhaseControl.writtenRef, LatticeMetricMachine.basisCellInput,
      LatticeState.coordinateInput, CInputRef.storageKeys, List.mem_singleton,
      LatticeState.MachineRefs.keyOf, phaseMachineCell, basisMachineCell] using keyNe

/-- An actual phase update preserves the complete represented basis. -/
theorem transition_basis (refs : Refs ctx width) (separation : Separation refs)
    (transition : LatticePhaseControl.Transition) (store : Store ctx)
    (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (store.applyOp (LatticePhaseControl.transitionOp refs.machine transition))
      refs.machine.basis basis :=
  basis_of_frames refs basis (fun cell => LatticePhaseControl.transitionInto_callerFrame
    refs.machine transition store _ (phase_avoids_basis refs separation transition cell)) rep

/-- The actual Gram refresh retains the original phase encoding. -/
theorem refresh_phase (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (phase : NumberTheory.LLLPhase3)
    (rep : refs.machine.PhaseRepresents store phase) :
    refs.machine.PhaseRepresents
      (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric store) phase :=
  phase_of_frames refs phase
    (LatticeMetricMachine.refreshInto_callerFrame _ _ _ _ separation.secondPhaseMetric)
    (LatticeMetricMachine.refreshInto_callerFrame _ _ _ _ separation.doneMetric) rep

/-- Shared Gram identities are already excluded by the original first-pair caller frame. -/
theorem caller_avoids_metric (refs : Refs ctx width) {shape : CShape}
    (other : CInputRef ctx shape) (separate : CallerSeparated refs other)
    (cell : LatticeMetricMachine.MetricCell) :
    LatticeMetricMachine.metricCellKey refs.metric cell ∉ other.storageKeys := by
  have frame := separate.first (LatticeFirstPairMachine.metricTransitionCell cell)
  cases cell <;>
    simpa only [LatticeFirstPairMachine.metricTransitionCell, LatticeFirstPairMachine.cellKey,
      refs.firstMetric, LatticeMetricMachine.metricCellKey,
      LatticeMetricMachine.metricCellRef] using frame

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Either actual first latch arm preserves the original complete caller frame. -/
theorem firstAdvanceArm_frame (refs : Refs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : CallerSeparated refs other) :
    (firstAdvanceArmStep (model := model) refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · rfl
    · exact LatticePhaseControl.transitionInto_callerFrame refs.machine .firstPass store other
        separate.secondPhase

/-- The actually selected first latch update preserves every separated caller read. -/
theorem firstAdvance_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (firstAdvanceStep (model := model) refs store).1.read other = store.read other :=
  firstAdvanceArm_frame refs _ store other separate

/-- Actual first latch update and Gram refresh preserve the caller's original read frame. -/
theorem firstTail_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (firstTailStep (model := model) refs store).1.read other = store.read other := by
  change (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric
    (firstAdvanceStep (model := model) refs store).1).read other = _
  rw [LatticeMetricMachine.refreshInto_callerFrame _ _ _ other
    (caller_avoids_metric refs other separate), firstAdvance_frame refs store other separate]

/-- The complete actual first driver arm preserves every original separated caller read. -/
theorem firstStep_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (firstStep (model := model) refs store).1.read other = store.read other := by
  change (firstTailStep (model := model) refs
    (LatticeFirstPairMachine.firstPairStep (model := model) refs.first store).1).1.read
    other = _
  rw [firstTail_frame refs _ other separate]
  exact LatticeFirstPairMachine.firstPairInto_callerFrame refs.first store other
    (fun cell _ => separate.first cell)

/-- Either actual second latch arm preserves the original complete caller frame. -/
theorem secondAdvanceArm_frame (refs : Refs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (separate : CallerSeparated refs other) :
    (secondAdvanceArmStep (model := model) refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticePhaseControl.transitionInto_callerFrame refs.machine .secondFail store other
        separate.secondPhase
    · exact LatticePhaseControl.transitionInto_callerFrame refs.machine .secondPass store other
        separate.done

/-- The actually selected second latch update preserves every separated caller read. -/
theorem secondAdvance_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (secondAdvanceStep (model := model) refs store).1.read other = store.read other :=
  secondAdvanceArm_frame refs _ store other separate

/-- Actual second latch update and Gram refresh preserve the caller's original read frame. -/
theorem secondTail_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (secondTailStep (model := model) refs store).1.read other = store.read other := by
  change (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric
    (secondAdvanceStep (model := model) refs store).1).read other = _
  rw [LatticeMetricMachine.refreshInto_callerFrame _ _ _ other
    (caller_avoids_metric refs other separate), secondAdvance_frame refs store other separate]

/-- The complete actual second driver arm preserves every original separated caller read. -/
theorem secondStep_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (secondStep (model := model) refs store).1.read other = store.read other := by
  change (secondTailStep (model := model) refs
    (LatticeSecondPairFullMachine.secondPairStep (model := model) refs.second store).1).1.read
    other = _
  rw [secondTail_frame refs _ other separate]
  exact LatticeSecondPairFullMachine.secondPairInto_callerFrame refs.second store other
    (fun cell _ => separate.second cell)

/-- The actual phase-selected pair retains the complete original caller frame. -/
theorem nonDoneStep_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (nonDoneStep (model := model) refs store).1.read other = store.read other := by
  change (nonDoneArmStep (model := model) refs
    (store.read (phaseInput refs.machine.secondPhase)) store).1.read
    other = _
  cases store.read (phaseInput refs.machine.secondPhase) with
  | bit flag =>
    cases flag
    · exact firstStep_frame refs store other separate
    · exact secondStep_frame refs store other separate

/-- Terminal identity or the actual nonterminal step preserves the same complete caller frame. -/
theorem step_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (step (model := model) refs store).1.read other = store.read other := by
  change (stepArmStep (model := model) refs
    (store.read (phaseInput refs.machine.done)) store).1.read other = _
  cases store.read (phaseInput refs.machine.done) with
  | bit flag =>
    cases flag
    · exact nonDoneStep_frame refs store other separate
    · rfl

/-- Every finite number of actual LLL iterations retains every original separated caller read. -/
theorem fixedFuelInto_callerFrame (fuel : Nat) (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : CallerSeparated refs other) :
    (fixedFuelStep (model := model) fuel refs store).1.read other = store.read other := by
  change ((fun current => (step (model := model) refs current).1)^[fuel] store).read other = _
  induction fuel generalizing store with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, ih, step_frame refs store other separate]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
