/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Phase.Prelude
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Tail

/-!
# Actual first-phase left shift and complete ordered control suffix

Both phase bits zero select exactly the real one-bit left rotation and
finite increment. The strict comparison subsequently moves from Sign to
Phase2 under the source's ordered update, clearing Sign
[LYL+26, sec_EEA/sub_opt.tex:37-50,61-79]. The comparison therefore controls
entry to division through the actual stored flag, not a separate loop oracle.

The native Sign/quotient, coefficient, post-shift, zero-shift, and boundary
lists remain present. Their complete-state equations below show precisely
which actual data branches are inactive before that division transition.
Positive retained shift and live divisor are internal trajectory facts;
the original caller has no new clean-work or phase assumptions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AlignmentPrelude

noncomputable section

/-- The real first-phase pre-shift rotates the whole word once and increments its finite counter. -/
theorem pre_shift (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = false)
    (within : state.shift.toNat + 1 < 2 ^ width.size) :
    GuardedShift.step false state =
      { state with secondWord := state.secondWord.rotateLeft 1, shift := state.shift + 1 } := by
  rw [GuardedShift.step_eq_source width false state clean, GuardedShift.sourceStep,
    first, if_pos rfl, second]
  exact GuardedShift.ascending_eq_low state within

/-- Ordered actual control moves the computed comparison to Phase2 and clears its original Sign. -/
theorem control_frame {width : Nat} (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = false) (quotient : state.quotientLength = (0#width.size))
    (divisor : state.divisorLength ≠ (0#width.size)) :
    NativeControl.step state =
      { state with flags := ⟨false, state.flags.sign, false, state.flags.iteration⟩ } := by
  rw [NativeControl.step_eq_sourceStep state clean]
  change { state with flags := (NumberTheory.SharedEEA.PhaseControl.update
    (decide (state.quotientLength = (0#width.size)))
    (decide (state.divisorLength ≠ (0#width.size))) false state.flags) } = _
  rw [decide_eq_true quotient, decide_eq_true divisor]
  unfold NumberTheory.SharedEEA.PhaseControl.update
  rw [first, second]
  cases state.flags.sign <;> rfl

/-- Every actual block after alignment arithmetic leaves only the computed phase transition. -/
theorem tail_frame (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = false) (quotient : state.quotientLength = (0#width.size))
    (divisor : state.divisorLength ≠ (0#width.size)) (shift : state.shift ≠ (0#width.size)) :
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
      (GuardedShift.step true (ArithmeticBlocks.coefficientStep width
        (SignQuotient.step width state))))) =
      { state with flags := ⟨false, state.flags.sign, false, state.flags.iteration⟩ } := by
  rw [DeshiftPhasePrelude.quotient_inactive width state clean (first.trans second.symm),
    DivisionTail.coefficient_inactive width state clean first,
    DivisionTail.post_shift_inactive width state clean first,
    CoefficientTail.zero_shift_inactive (NativeControl.step state) clean shift,
    CoefficientTail.boundary_inactive (NativeControl.step state) clean shift]
  exact control_frame state clean first second quotient divisor

end

end QuantumAlg.MAU.Inversion.SharedEEA.AlignmentPrelude
