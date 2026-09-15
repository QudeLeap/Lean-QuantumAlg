/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Microstep

/-!
# Actual inactive prefix and ordered coefficient-phase control suffix

Phase1 one disables the pre-shift and remainder arithmetic before the
source consumes its next quotient bit. After coefficient arithmetic and
its positive post-shift, the actual ordered phase update enters phase four
when the quotient becomes empty, with Sign equal to one
[LYL+26, sec_EEA/sub_opt.tex:37-48,68-84;
LYL+26, sec_EEA/sub_regshare.tex:288-305]. Keeping Sign zero at that boundary
would disagree with these actual source assignments.

These complete-state equations use the existing native blocks. All native
events remain present even on inactive data branches. Positivity of the
post-shift, the live divisor, and clean Ctrl are internal reachable-frame
invariants; no terminal idle rule or final-caller condition is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.CoefficientTail

noncomputable section

private theorem subtract_inactive {width : Nat} (state : Registers width)
    (first : state.flags.first = true) :
    ArithmeticInstruction.sourceStep .remainderSubtract state = state := by
  simp only [ArithmeticInstruction.sourceStep, ArithmeticInstruction.sourceEnabled,
    ArithmeticInstruction.sourcePhaseEnabled,
    first, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]

private theorem addback_inactive {width : Nat} (state : Registers width)
    (first : state.flags.first = true) :
    ArithmeticInstruction.sourceStep .remainderAddback state = state := by
  simp only [ArithmeticInstruction.sourceStep, ArithmeticInstruction.sourceEnabled,
    ArithmeticInstruction.sourcePhaseEnabled,
    first, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false]

/-- The actual remainder arithmetic is inactive in coefficient phase and retains the whole state. -/
theorem remainder_inactive (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true) :
    ArithmeticBlocks.remainderStep width state = state := by
  have sign : ArithmeticSign.remainderStep state = state := by
    have unchanged : (state.flags.sign ^^ (!state.flags.first && state.flags.second)) =
        state.flags.sign := by
      rw [first, Bool.not_true, Bool.false_and, Bool.xor_false]
    unfold ArithmeticSign.remainderStep
    rw [unchanged]
  rw [ArithmeticBlocks.remainderStep_eq_source width state clean,
    ArithmeticBlocks.remainderSource, subtract_inactive state first,
    sign, addback_inactive state first]

/-- The actual pre-shift is inactive in coefficient phase, before the real quotient exchange. -/
theorem pre_shift_inactive (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true) :
    GuardedShift.step false state = state := by
  rw [GuardedShift.step_eq_source width false state clean, GuardedShift.sourceStep]
  exact if_neg (by rw [first]; decide)

/-- Positive actual shift disables the real zero-shift phase complements. -/
theorem zero_shift_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (shift : state.shift ≠ (0#width.size)) :
    ZeroShiftControl.step state = state := by
  rw [ZeroShiftControl.step_eq_sourceStep state clean]
  have unselected : TerminalPredicate.condition state = false :=
    decide_eq_false (fun selected => shift selected.1)
  simp only [ZeroShiftControl.sourceStep, unselected, Bool.false_eq_true, if_false]

/-- The real boundary exchange cannot occur while the actual shift field is nonzero. -/
theorem boundary_inactive {width : Nat} (state : Registers width)
    (clean : state.control = false) (shift : state.shift ≠ (0#width.size)) :
    TerminalBoundary.step state = state := by
  apply TerminalBoundary.step_unselected state clean
  exact decide_eq_false (fun selected => shift selected.2.1)

/-- The actual ordered update sets both Phase2 and Sign to the actual quotient-empty predicate. -/
theorem control_frame {width : Nat} (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false) (sign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ (0#width.size)) :
    NativeControl.step state = { state with flags :=
      ⟨true, decide (state.quotientLength = (0#width.size)),
        decide (state.quotientLength = (0#width.size)), state.flags.iteration⟩ } := by
  have flags : NumberTheory.SharedEEA.PhaseControl.update
      (decide (state.quotientLength = (0#width.size))) true false state.flags =
        ⟨true, decide (state.quotientLength = (0#width.size)),
          decide (state.quotientLength = (0#width.size)), state.flags.iteration⟩ := by
    unfold NumberTheory.SharedEEA.PhaseControl.update
    rw [first, second, sign]
    cases decide (state.quotientLength = (0#width.size)) <;> rfl
  rw [NativeControl.step_eq_sourceStep state clean]
  change { state with flags := (NumberTheory.SharedEEA.PhaseControl.update
    (decide (state.quotientLength = (0#width.size)))
    (decide (state.divisorLength ≠ (0#width.size))) false state.flags) } = _
  rw [decide_eq_true divisor, flags]

/-- The actual complete control suffix preserves every other field and reaches the source phases. -/
theorem tail_frame {width : Nat} (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = true)
    (second : state.flags.second = false) (sign : state.flags.sign = false)
    (divisor : state.divisorLength ≠ (0#width.size)) (shift : state.shift ≠ (0#width.size)) :
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step state)) =
      { state with flags :=
        ⟨true, decide (state.quotientLength = (0#width.size)),
          decide (state.quotientLength = (0#width.size)), state.flags.iteration⟩ } := by
  rw [zero_shift_inactive (NativeControl.step state) clean shift,
    boundary_inactive (NativeControl.step state) clean shift]
  exact control_frame state clean first second sign divisor

end

end QuantumAlg.MAU.Inversion.SharedEEA.CoefficientTail
