/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Microstep.Body

/-!
# Original Iter history certifies when the full final boundary is identity

This is a semantic criterion on the same original full source action.
The actual first seven blocks retain Iter; the final boundary changes it
exactly when its real predicate is selected. Static omitted positions
still require their independently derived source-trajectory invariant.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep

noncomputable section

open EncodedBit

private lemma shift_iteration (width : Nat) (selected : Bool) (state : Registers width) :
    (GuardedShift.step selected state).flags.iteration = state.flags.iteration := by
  have first (value : Registers width) :
      (GuardedShift.firstStep selected value).flags.iteration = value.flags.iteration := by
    unfold GuardedShift.firstStep
    split <;> rfl
  have last (value : Registers width) :
      (GuardedShift.lastStep selected value).flags.iteration = value.flags.iteration := by
    unfold GuardedShift.lastStep
    split <;> rfl
  rw [GuardedShift.step, last, first]

private lemma exchange_iteration (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (SelectionSwap.exchange width index state).flags.iteration = state.flags.iteration := by
  have signIter : (SharedEEA.signBit width).wire ≠ (SharedEEA.iterationBit width).wire := by
    intro same
    have values := congrArg Fin.val same
    rw [SharedEEA.signBit_wire, SharedEEA.iterationBit_wire] at values
    omega
  have wordIter : (SharedEEA.firstWordBit width index).wire ≠
      (SharedEEA.iterationBit width).wire := by
    intro same
    have values := congrArg Fin.val same
    rw [SharedEEA.firstWordBit_wire, SharedEEA.iterationBit_wire] at values
    have within := index.isLt
    omega
  exact swapStep_get_observed_of_swap_ne (SharedEEA.signBit width)
    (SharedEEA.firstWordBit width index) (SharedEEA.iterationBit width)
    (SelectionSwap.sign_word width index) signIter wordIter state

private lemma sign_iteration (width : Nat) (state : Registers width)
    (control : state.control = false) :
    (SharedEEA.SignQuotient.step width state).flags.iteration = state.flags.iteration := by
  rw [SharedEEA.SignQuotient.step_eq_sourceStep width state control]
  change (SelectionSchedule.sourceStep width state).flags.iteration = state.flags.iteration
  unfold SelectionSchedule.sourceStep
  split <;> split
  · split
    · exact exchange_iteration width _ state
    · rfl
  · rfl
  · split
    · exact exchange_iteration width _ state
    · rfl
  · rfl

private lemma control_iteration (width : Nat) (state : Registers width) :
    (NativeControl.step state).flags.iteration = state.flags.iteration := by
  unfold NativeControl.step
  split <;> rfl

private lemma zero_iteration (width : Nat) (state : Registers width) :
    (ZeroShiftControl.step state).flags.iteration = state.flags.iteration := rfl

/-- All actual original work, arithmetic and phase actions preceding the boundary retain Iter. -/
lemma bodyStep_iteration (width : Nat) (state : Registers width) (control : state.control = false) :
    (bodyStep width state).flags.iteration = state.flags.iteration := by
  have afterRemainder :
      (SharedEEA.ArithmeticBlocks.remainderStep width
        (GuardedShift.step false state)).control = false :=
    (SharedEEA.ArithmeticBlocks.remainderStep_control width _).trans
      ((GuardedShift.step_control width false state).trans control)
  rw [bodyStep, zero_iteration, control_iteration, shift_iteration,
    SharedEEA.ArithmeticBlocks.coefficientStep_iteration, sign_iteration width _ afterRemainder,
    SharedEEA.ArithmeticBlocks.remainderStep_iteration, shift_iteration]

/-- The actual complete boundary's Iter toggle is exactly its real predicate from clean Ctrl. -/
lemma boundary_iteration (width : Nat) (state : Registers width) (control : state.control = false) :
    (SharedEEA.TerminalBoundary.step state).flags.iteration =
      (state.flags.iteration ^^ BoundaryPredicate.condition state) := by
  cases selected : BoundaryPredicate.condition state with
  | false =>
      have actual := congrArg (fun result : Registers width => result.flags.iteration)
        (SharedEEA.TerminalBoundary.step_unselected state control selected)
      exact actual.trans (Bool.xor_false state.flags.iteration).symm
  | true =>
      have actual := congrArg (fun result : Registers width => result.flags.iteration)
        (SharedEEA.TerminalBoundary.step_selected state control selected)
      change (SharedEEA.TerminalBoundary.step state).flags.iteration =
        !state.flags.iteration at actual
      exact actual.trans (Bool.xor_true state.flags.iteration).symm

private lemma iteration_mask_false_of_xor_fixed (value mask : Bool)
    (same : (value ^^ mask) = value) :
    mask = false := by
  cases value <;> cases mask <;> simp_all

/-- An unchanged reached Iter certifies identity of the same full final boundary. -/
lemma source_step_eq_body_of_iteration (width : Nat) (state : Registers width)
    (control : state.control = false)
    (same : (SharedEEA.NativeMicrostep.step width state).flags.iteration = state.flags.iteration) :
    SharedEEA.NativeMicrostep.step width state = bodyStep width state := by
  have bodyControl := (bodyStep_control width state).trans control
  have bodyIteration := bodyStep_iteration width state control
  have actual := boundary_iteration width (bodyStep width state) bodyControl
  change (SharedEEA.TerminalBoundary.step (bodyStep width state)).flags.iteration =
    state.flags.iteration at same
  have fixed := actual.symm.trans (same.trans bodyIteration.symm)
  have unselected := iteration_mask_false_of_xor_fixed _ _ fixed
  rw [source_step_eq_boundary,
    SharedEEA.TerminalBoundary.step_unselected (bodyStep width state) bodyControl unselected]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeMicrostep
