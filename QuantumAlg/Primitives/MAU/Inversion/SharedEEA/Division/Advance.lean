/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Packing
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Retained
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Tail
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.RegisterFrame

/-!
# Complete actual division frame after arithmetic and the remaining microstep

The actual remainder block and Sign/quotient program advance the entire
packed Work1 state, increment the live quotient length, clear Sign, and
retain Work2, coefficient/divisor/shift lengths, both phases, arbitrary
Iter, and Ctrl [LYL+26, sec_EEA/sub_regshare.tex:279-287]. The equations
below reassemble all eleven actual register fields, rather than only the
remainder readout.

The remaining actual source instructions then enter coefficient phase
precisely when the actual low shift reaches zero
[LYL+26, sec_EEA/sub_opt.tex:61-84]. The stated frame is a basis-state
specification for refinement of existing programs, never input-dependent
preparation or another interpreter. The pre-shift entry and full repaired
terminal schedule remain separately connected obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DivisionAdvance

noncomputable section

open ArithmeticWindowRegisters RemainderPhaseFrame NumberTheory.SharedEEA

private lemma next_count_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    count + 1 < 2 ^ modulus.size.size :=
  (show count + 1 ≤ modulus.size by
    have bound := RemainderPhaseFrame.alignment_le state modulus valid conserved
    omega).trans_lt (Nat.lt_size_self modulus.size)

/-- Complete expected basis frame after actual division arithmetic and quotient exchange. -/
def nextFrame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) : Registers modulus.size :=
  { frame state modulus count valid conserved active beforeEnd iteration with
    firstWord := (WordPacking.packWork1
      (DivisionCapacity.work1Payload state modulus (count + 1)
        valid conserved active (by omega))).cast
          (DivisionCapacity.work1_width state modulus (count + 1)
            valid conserved active (by omega))
    quotientLength := BitVec.ofNatLT (count + 1)
      (next_count_fits state modulus count valid conserved beforeEnd) }

private lemma native_firstWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).firstWord =
        (nextFrame state modulus count valid conserved active beforeEnd iteration).firstWord := by
  change (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).firstWord =
    (WordPacking.packWork1 (DivisionCapacity.work1Payload state modulus (count + 1)
      valid conserved active (by omega))).cast
        (DivisionCapacity.work1_width state modulus (count + 1)
          valid conserved active (by omega))
  exact RemainderPhasePacking.native_firstWord state modulus count
    valid conserved active beforeEnd iteration

/-- Exact complete-state refinement of the existing native arithmetic and quotient programs. -/
lemma native_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)) =
        nextFrame state modulus count valid conserved active beforeEnd iteration := by
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let middle := ArithmeticBlocks.remainderStep modulus.size original
  let output := SignQuotient.step modulus.size middle
  let expected := nextFrame state modulus count valid conserved active beforeEnd iteration
  let selected := window state modulus count valid conserved active beforeEnd
  have fields := RemainderPhaseExchange.native_fields state modulus count
    valid conserved active beforeEnd iteration
  have position := RemainderPhaseExchange.next_position state modulus count
    valid conserved active beforeEnd iteration
  have retained := congrArg (fun value : Complement selected => value.2.2)
    (RemainderPhaseAction.native_complement state modulus count
      valid conserved active beforeEnd iteration)
  have selection : output.coefficientLength = middle.coefficientLength ∧
      output.flags.first = false ∧ output.flags.second = true := by
    change (SignQuotient.step modulus.size middle).coefficientLength = middle.coefficientLength ∧
      (SignQuotient.step modulus.size middle).flags.first = false ∧
        (SignQuotient.step modulus.size middle).flags.second = true
    rw [SignQuotient.step_eq_sourceStep modulus.size middle fields.2.2.2.2]
    exact SignQuotientFields.source_retained modulus.size middle
      fields.2.2.1 fields.2.2.2.1 position.1
  have extra := RemainderRetained.native_extra modulus.size middle
    fields.2.2.2.2 fields.2.2.1 fields.2.2.2.1 position.1
  apply Registers.ext_fields output expected
  · exact native_firstWord state modulus count valid conserved active beforeEnd iteration
  · exact RemainderRetained.division_secondWord modulus.size original rfl rfl rfl
      (window_fits state modulus count valid conserved active beforeEnd)
  · exact selection.1.trans
      (congrArg (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.1.1)
        retained)
  · apply BitVec.eq_of_toNat_eq
    exact SignQuotientFields.division_quotientLength_toNat state modulus count
      valid conserved active beforeEnd iteration
  · exact extra.1.trans
      (congrArg (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.1.1)
        retained)
  · exact extra.2.1.trans
      (congrArg (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.1.2)
        retained)
  · exact selection.2.1
  · exact selection.2.2
  · exact RemainderPhaseExchange.native_sign_clear state modulus count
      valid conserved active beforeEnd iteration
  · exact extra.2.2.trans
      (congrArg (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.2.1)
        retained)
  · exact (SignQuotient.step_control modulus.size middle).trans fields.2.2.2.2

private lemma next_quotient_nonzero (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (nextFrame state modulus count valid conserved active beforeEnd iteration).quotientLength ≠
      (0#modulus.size.size) := by
  intro zero
  have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
  change count + 1 = 0 at value
  omega

/-- The rest of the same actual microstep preserves this full frame except its two phase bits. -/
lemma native_tail_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    let after := SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))
    let expected := nextFrame state modulus count valid conserved active beforeEnd iteration
    TerminalBoundary.step (ZeroShiftControl.step (NativeControl.step
      (GuardedShift.step true (ArithmeticBlocks.coefficientStep modulus.size after)))) =
      { expected with flags :=
        ⟨decide (expected.shift = (0#modulus.size.size)),
          !decide (expected.shift = (0#modulus.size.size)), false, iteration⟩ } := by
  dsimp only
  rw [native_frame state modulus count valid conserved active beforeEnd iteration]
  have divisor : (nextFrame state modulus count valid conserved active
      beforeEnd iteration).divisorLength ≠ 0 := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change state.divisor.size = 0 at value
    have positive := Nat.size_pos.mpr active
    omega
  exact DivisionTail.tail_frame modulus.size
    (nextFrame state modulus count valid conserved active beforeEnd iteration) rfl rfl rfl
      (next_quotient_nonzero state modulus count valid conserved active beforeEnd iteration) divisor

end

end QuantumAlg.MAU.Inversion.SharedEEA.DivisionAdvance
