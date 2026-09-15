/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Coefficient.Tail

/-!
# Actual inactive prefix and post-shift of a fourth-phase microstep

Equal phase bits disable the real Sign/quotient exchange and its length
update. In phase four the source's post-shift executes one left rotation
and increment, followed by two right rotations and decrements
[LYL+26, sec_EEA/sub_opt.tex:50-70]. Their complete finite-word composition
is exactly one right rotation and decrement, including intermediate wrap.

These are equations of existing native components, with all emitted gates
still present and every dirty-work bit restored. The full coefficient
comparison and its integer interpretation are supplied by their own owners.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftPhasePrelude

noncomputable section

/-- Equal actual phases make the native Sign/quotient block inactive on the complete frame. -/
theorem quotient_inactive (width : Nat) (state : Registers width)
    (clean : state.control = false) (same : state.flags.first = state.flags.second) :
    SignQuotient.step width state = state := by
  have selected : SelectionKey.phaseSelected state = false := by
    unfold SelectionKey.phaseSelected
    rw [same, Bool.xor_self]
  have exchange : SelectionSchedule.sourceStep width state = state := by
    unfold SelectionSchedule.sourceStep
    split
    · split
      · exact if_neg (by rw [selected]; decide)
      · rfl
    · split
      · exact if_neg (by rw [selected]; decide)
      · rfl
  rw [SignQuotient.step_eq_sourceStep width state clean, SignQuotient.sourceStep, exchange]
  change { state with quotientLength :=
    (if state.flags.first ^^ state.flags.second then
      if state.flags.first then state.quotientLength - 1 else state.quotientLength + 1
    else state.quotientLength) } = state
  simp only [same, Bool.xor_self, Bool.false_eq_true, if_false]

/-- Actual phase-four post-shifts compose to a full-word right rotation and finite decrement. -/
theorem post_shift (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = true) (positive : 0 < state.shift.toNat) :
    GuardedShift.step true state =
      { state with secondWord := state.secondWord.rotateRight 1, shift := state.shift - 1 } := by
  rw [GuardedShift.step_eq_source width true state clean, GuardedShift.sourceStep,
    first, if_pos rfl, second]
  change GuardedShift.descending (GuardedShift.ascending state) = _
  rw [GuardedShift.descending_ascending_eq_low state positive,
    NumberTheory.SharedEEA.WordRotation.rotateRight_rotateLeft]

/-- Ordered native control retains phase four and clears its actual comparison Sign one. -/
theorem control_clears {width : Nat} (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = true) (sign : state.flags.sign = true)
    (quotient : state.quotientLength = (0#width.size))
    (divisor : state.divisorLength ≠ (0#width.size)) :
    NativeControl.step state =
      { state with flags := ⟨true, true, false, state.flags.iteration⟩ } := by
  rw [NativeControl.step_eq_sourceStep state clean]
  change { state with flags := (NumberTheory.SharedEEA.PhaseControl.update
    (decide (state.quotientLength = (0#width.size)))
    (decide (state.divisorLength ≠ (0#width.size))) false state.flags) } = _
  rw [decide_eq_true quotient, decide_eq_true divisor]
  unfold NumberTheory.SharedEEA.PhaseControl.update
  rw [first, second, sign]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftPhasePrelude
