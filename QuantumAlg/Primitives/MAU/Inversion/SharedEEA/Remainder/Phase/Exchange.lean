/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Action
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Exchange

/-!
# Actual phase-two arithmetic followed by native Sign and quotient exchange

The source writes the computed comparison digit into the next quotient
position and only then interprets the remaining lower region at its new
width [LYL+26, sec_EEA/sub_regshare.tex:279-287]. The native source ordering
is the existing remainder block followed by the existing `SignQuotient`
program. The proofs below retain that order and use the actual intermediate
frame, including its full old remainder and arbitrary original Iter.

Reachable next-state capacity establishes that the exchanged old top bit
is zero. Thus the actual Sign clears, and the complete old-width output
word agrees with the previously proved signed division instruction. No
caller supplies a clean Sign, work word, arithmetic range, or next-state
certificate. Full macro-loop and terminal dispatch remain separate duties.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseExchange

noncomputable section

open ArithmeticWindowRegisters RemainderReassembly RemainderPhaseFrame
open NumberTheory.SharedEEA

private lemma read_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (window state modulus count valid conserved active beforeEnd).length +
        (window state modulus count valid conserved active beforeEnd).below =
      SignedDivisionPhase.nextWidth state modulus count + 1 :=
  (remainder_width state modulus count valid conserved active beforeEnd).trans
    (DivisionThreshold.remainder_width_succ state modulus count valid conserved active beforeEnd)

private lemma native_old_read (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).firstWord.setWidth
        (SignedDivisionPhase.nextWidth state modulus count + 1)).toNat =
      (DivisionProgress.current state (count + 1)).remainder := by
  let selected := window state modulus count valid conserved active beforeEnd
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have read := RemainderPhaseAction.native_remainder state modulus count
    valid conserved active beforeEnd iteration
  change (after.firstWord.extractLsb' 0 (selected.length + selected.below)).toNat = _ at read
  have size := read_width state modulus count valid conserved active beforeEnd
  change selected.length + selected.below =
    SignedDivisionPhase.nextWidth state modulus count + 1 at size
  have complete := selected.complete
  have bound : SignedDivisionPhase.nextWidth state modulus count + 1 ≤ modulus.size + 3 := by
    omega
  have castRead : after.firstWord.setWidth (SignedDivisionPhase.nextWidth state modulus count + 1) =
      after.firstWord.extractLsb' 0 (SignedDivisionPhase.nextWidth state modulus count + 1) :=
    BitVec.setWidth_eq_extractLsb' bound
  exact (congrArg BitVec.toNat castRead).trans
    ((congrArg (fun width => (after.firstWord.extractLsb' 0 width).toNat) size).symm.trans read)

private lemma native_low_read (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)).firstWord.setWidth
        (SignedDivisionPhase.nextWidth state modulus count)).toNat =
      (DivisionProgress.current state (count + 1)).remainder := by
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  let width := SignedDivisionPhase.nextWidth state modulus count
  have fits : (DivisionProgress.current state (count + 1)).remainder < 2 ^ width :=
    DivisionCapacity.remainder_fits state modulus (count + 1) valid conserved active (by omega)
  have read := native_old_read state modulus count valid conserved active beforeEnd iteration
  change (after.firstWord.setWidth (width + 1)).toNat = _ at read
  have narrowed : ((after.firstWord.setWidth (width + 1)).setWidth width).toNat =
      (DivisionProgress.current state (count + 1)).remainder := by
    rw [BitVec.toNat_setWidth, read, Nat.mod_eq_of_lt fits]
  have collapse : (after.firstWord.setWidth (width + 1)).setWidth width =
      after.firstWord.setWidth width :=
    BitVec.setWidth_setWidth_of_le after.firstWord (by omega)
  exact (congrArg BitVec.toNat collapse).symm.trans narrowed

private lemma native_fields (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    let after := ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)
    after.coefficientLength.toNat = state.coefficient.size ∧
      after.quotientLength.toNat = count ∧ after.flags.first = false ∧
        after.flags.second = true ∧ after.control = false := by
  dsimp only
  let selected := window state modulus count valid conserved active beforeEnd
  have retained := congrArg (fun value : Complement selected => value.2.2)
    (RemainderPhaseAction.native_complement state modulus count
      valid conserved active beforeEnd iteration)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.1.1.toNat) retained
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.1.2.toNat) retained
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.1.1) retained
  · exact congrArg
      (fun value : ArithmeticWindowPreservation.Retained modulus.size => value.2.2.1.2) retained
  · exact ArithmeticBlocks.remainderStep_control modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)

private lemma next_position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    let after := ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration)
    after.coefficientLength.toNat + after.quotientLength.toNat + 1 < modulus.size + 3 ∧
      modulus.size + 3 - 1 - (after.coefficientLength.toNat + after.quotientLength.toNat + 1) =
        SignedDivisionPhase.nextWidth state modulus count := by
  dsimp only
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have fields := native_fields state modulus count valid conserved active beforeEnd iteration
  change after.coefficientLength.toNat = state.coefficient.size ∧
    after.quotientLength.toNat = count ∧ _ at fields
  have capacity := DivisionCapacity.work1_capacity state modulus (count + 1)
    valid conserved active (by omega)
  rw [DivisionProgress.current_written] at capacity
  change after.coefficientLength.toNat + after.quotientLength.toNat + 1 < modulus.size + 3 ∧ _
  rw [fields.1, fields.2.1]
  unfold SignedDivisionPhase.nextWidth DivisionCapacity.remainderWidth
  rw [DivisionProgress.current_written]
  omega

/-- Actual subtraction and the subsequent native exchange clear Sign at every reachable position. -/
lemma native_sign_clear (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).flags.sign =
        false := by
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have fields := native_fields state modulus count valid conserved active beforeEnd iteration
  have position := next_position state modulus count valid conserved active beforeEnd iteration
  have fits : (after.firstWord.setWidth (modulus.size + 3 - 1 -
      (after.coefficientLength.toNat + after.quotientLength.toNat + 1) + 1)).toNat <
        2 ^ (modulus.size + 3 - 1 -
          (after.coefficientLength.toNat + after.quotientLength.toNat + 1)) := by
    rw [position.2, native_old_read]
    exact DivisionCapacity.remainder_fits state modulus (count + 1)
      valid conserved active (by omega)
  have cleared := RemainderExchange.source_sign_clear modulus.size after
    fields.2.2.1 fields.2.2.2.1 position.1 fits
  exact (congrArg (fun value : Registers modulus.size => value.flags.sign)
    (SignQuotient.step_eq_sourceStep modulus.size after fields.2.2.2.2)).trans cleared

/-- The same actual two native blocks produce the complete old-width signed-instruction word. -/
lemma native_word (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).firstWord.setWidth
        (SignedDivisionPhase.nextWidth state modulus count + 1) =
      (SignedDivisionPhase.instruction state modulus count valid conserved active beforeEnd).2 := by
  let after := ArithmeticBlocks.remainderStep modulus.size
    (frame state modulus count valid conserved active beforeEnd iteration)
  have fields := native_fields state modulus count valid conserved active beforeEnd iteration
  have position := next_position state modulus count valid conserved active beforeEnd iteration
  have actual := RemainderExchange.native_word modulus.size after
    fields.2.2.2.2 fields.2.2.1 fields.2.2.2.1 position.1
  change (SignQuotient.step modulus.size after).firstWord.setWidth
      (modulus.size + 3 - 1 -
        (after.coefficientLength.toNat + after.quotientLength.toNat + 1) + 1) =
    BitVec.cons after.flags.sign (after.firstWord.setWidth
      (modulus.size + 3 - 1 -
        (after.coefficientLength.toNat + after.quotientLength.toNat + 1))) at actual
  rw [position.2] at actual
  have expected := SignedDivisionPhase.instruction_spec state modulus count
    valid conserved active beforeEnd
  have digit := RemainderPhaseAction.native_digit state modulus count
    valid conserved active beforeEnd iteration
  have low := native_low_read state modulus count valid conserved active beforeEnd iteration
  have sameLow : after.firstWord.setWidth (SignedDivisionPhase.nextWidth state modulus count) =
      (SignedDivisionPhase.instruction state modulus count
        valid conserved active beforeEnd).2.setWidth
        (SignedDivisionPhase.nextWidth state modulus count) :=
    BitVec.eq_of_toNat_eq (low.trans expected.2.2.symm)
  exact actual.trans ((congrArg₂ BitVec.cons (digit.trans expected.2.1.symm) sameLow).trans
    (BitVec.cons_msb_setWidth _))

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhaseExchange
