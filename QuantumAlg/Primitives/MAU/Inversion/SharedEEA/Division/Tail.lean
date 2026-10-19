/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Microstep

/-!
# Actual remaining native microstep after a phase-two quotient update

A real division step has Phase1 zero and a nonzero newly written quotient
length. The source's coefficient arithmetic and post-shift are therefore
inactive, and the zero-quotient phase update and boundary exchange are also
inactive [LYL+26, sec_EEA/sub_opt.tex:61-84]. The actual low-shift predicate
still executes and complements both phase bits precisely when the shift
reaches zero, entering coefficient phase three.

These are complete-state equations for the existing suffix of
`NativeMicrostep.step`. Every declared gate remains in that program and
its resource trace. The local nonzero quotient is supplied by the actual
division counter theorem; this is not an idle rule for terminal padding.
The repaired terminal clock and its dispatch remain separate obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DivisionTail

noncomputable section

private lemma coefficient_subtract_inactive {width : Nat} (state : Registers width)
    (first : state.flags.first = false) :
    ArithmeticInstruction.sourceStep .coefficientSubtract state = state := by
  simp only [ArithmeticInstruction.sourceStep, ArithmeticInstruction.sourceEnabled,
    ArithmeticInstruction.sourcePhaseEnabled,
    first, Bool.false_and, Bool.false_eq_true, if_false]

private lemma coefficient_add_inactive {width : Nat} (state : Registers width)
    (first : state.flags.first = false) :
    ArithmeticInstruction.sourceStep .coefficientAdd state = state := by
  simp only [ArithmeticInstruction.sourceStep, ArithmeticInstruction.sourceEnabled,
    ArithmeticInstruction.sourcePhaseEnabled,
    first, Bool.false_eq_true, if_false]

/-- The actual coefficient block is inactive during division and returns the complete frame. -/
lemma coefficient_inactive (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false) :
    ArithmeticBlocks.coefficientStep width state = state := by
  have sign : ArithmeticSign.coefficientStep state = state := by
    have unchanged : (state.flags.sign ^^ state.flags.first) = state.flags.sign := by
      rw [first, Bool.xor_false]
    unfold ArithmeticSign.coefficientStep
    rw [unchanged]
  rw [ArithmeticBlocks.coefficientStep_eq_source width state clean,
    ArithmeticBlocks.coefficientSource, coefficient_subtract_inactive state first,
    sign, coefficient_add_inactive state first]

/-- The actual post-arithmetic shift is inactive when Phase1 is zero. -/
lemma post_shift_inactive (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false) :
    GuardedShift.step true state = state := by
  rw [GuardedShift.step_eq_source width true state clean, GuardedShift.sourceStep]
  exact if_neg (by rw [first]; decide)

/-- A nonzero actual quotient length disables only the source's zero-quotient phase update. -/
lemma phase_update_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (quotient : state.quotientLength ≠ (0#width.size)) :
    NativeControl.step state = state := by
  rw [NativeControl.step_eq_sourceStep state clean]
  change { state with flags := (NumberTheory.SharedEEA.PhaseControl.update
    (decide (state.quotientLength = (0#width.size)))
    (decide (state.divisorLength ≠ (0#width.size))) false state.flags) } = state
  have unchanged : NumberTheory.SharedEEA.PhaseControl.update false
      (decide (state.divisorLength ≠ (0#width.size))) false state.flags = state.flags := rfl
  rw [decide_eq_false quotient, unchanged]

/-- Actual boundary exchange and length refresh stay inactive while quotient digits are retained. -/
lemma boundary_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (quotient : state.quotientLength ≠ (0#width.size)) :
    TerminalBoundary.step state = state := by
  apply TerminalBoundary.step_unselected state clean
  exact decide_eq_false (fun selected => quotient selected.1)

/-- The existing native suffix reduces exactly to its still-active shift-zero phase instruction. -/
lemma tail_eq (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (quotient : state.quotientLength ≠ (0#width.size)) :
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
      (GuardedShift.step true (ArithmeticBlocks.coefficientStep width state)))) =
        ZeroShiftControl.step state := by
  rw [coefficient_inactive width state clean first, post_shift_inactive width state clean first,
    phase_update_inactive state clean quotient]
  exact boundary_inactive (ZeroShiftControl.step state) clean quotient

/-- The remaining actual instructions enter phase three exactly at shift zero. -/
lemma tail_frame (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true) (quotient : state.quotientLength ≠ (0#width.size))
    (divisor : state.divisorLength ≠ 0) :
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
      (GuardedShift.step true (ArithmeticBlocks.coefficientStep width state)))) =
      { state with flags :=
        ⟨decide (state.shift = (0#width.size)), !decide (state.shift = (0#width.size)),
          state.flags.sign, state.flags.iteration⟩ } := by
  rw [tail_eq width state clean first quotient,
    ZeroShiftControl.step_eq_sourceStep state clean, ZeroShiftControl.sourceStep,
    TerminalPredicate.condition_active state divisor]
  change { state with flags :=
    ⟨if decide (state.shift = (0#width.size)) then !state.flags.first else state.flags.first,
      if decide (state.shift = (0#width.size)) then !state.flags.second else state.flags.second,
      state.flags.sign, state.flags.iteration⟩ } = _
  rw [first, second]
  cases decide (state.shift = (0#width.size)) <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.DivisionTail
