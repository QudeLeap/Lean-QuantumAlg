/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Remainder.Phase.Exchange
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.PackedStep

/-!
# Complete native Work1 transition at a division-phase position

The actual selector changes only Sign and the new quotient position;
every preceding coefficient, separator, and quotient-prefix bit is
retained [LYL+26, sec_EEA/sub_regshare.tex:279-287]. Combining that actual
prefix equation with the full native old-width output identifies the
entire original Work1 word after subtraction and Sign/quotient exchange.

The result is the next literal packed division state, with its longer
quotient and shorter remainder. The proof covers the complete shared word
and never replaces a boundary movement by a cardinality-only cast. The
original Iter and wrapped Work2 data remain in the already proved native
complement; the remaining phase-control and rotation instructions are
subsequent parts of the complete source microstep.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhasePacking

noncomputable section

open ArithmeticWindowRegisters RemainderPhaseFrame
open NumberTheory.SharedEEA

private lemma exchange_prefix (width : Nat) (selected : Fin (width + 3))
    (state : Registers width) :
    (SelectionSwap.exchange width selected state).firstWord.extractLsb'
        (width + 3 - 1 - selected.val + 1) selected.val =
      state.firstWord.extractLsb' (width + 3 - 1 - selected.val + 1) selected.val := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit within
  have selectedWithin := selected.isLt
  have sourceWithin : (width + 3 - 1 - selected.val + 1) + selected.val - bit ≤
      width + 3 := by omega
  have physical : width + 3 -
      ((width + 3 - 1 - selected.val + 1) + selected.val - bit) = bit := by omega
  have observedWithin : bit < width + 3 := by omega
  have different : selected ≠ (⟨bit, observedWithin⟩ : Fin (width + 3)) := by
    intro same
    have values := congrArg Fin.val same
    change selected.val = bit at values
    omega
  simp only [BitVec.getMsbD_extractLsb', within, sourceWithin, decide_true, Bool.true_and, physical]
  exact RemainderExchange.exchange_other width selected ⟨bit, observedWithin⟩ different state

private lemma native_prefix (width : Nat) (state : Registers width)
    (clean : state.control = false) (first : state.flags.first = false)
    (second : state.flags.second = true)
    (within : state.coefficientLength.toNat + state.quotientLength.toNat + 1 < width + 3) :
    let position := state.coefficientLength.toNat + state.quotientLength.toNat + 1
    (SignQuotient.step width state).firstWord.extractLsb' (width + 3 - 1 - position + 1) position =
      state.firstWord.extractLsb' (width + 3 - 1 - position + 1) position := by
  dsimp only
  rw [SignQuotient.step_eq_sourceStep width state clean]
  change (SelectionSchedule.sourceStep width state).firstWord.extractLsb' _ _ = _
  rw [RemainderExchange.selected_source width state first second within]
  exact exchange_prefix width
    ⟨state.coefficientLength.toNat + state.quotientLength.toNat + 1, within⟩ state

private lemma pack_prefix {coefficientWidth quotientWidth remainderWidth : Nat}
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth) :
    (WordPacking.packWork1 payload).extractLsb' remainderWidth
        ((coefficientWidth + 1) + quotientWidth) =
      (payload.coefficientBits.reverse ++ (0 : BitVec 1)) ++ payload.quotientBits := by
  let head := payload.coefficientBits.reverse ++ (0 : BitVec 1)
  have assemble : (head ++ payload.quotientBits) ++ payload.remainderBits =
      (head ++ (payload.quotientBits ++ payload.remainderBits)).cast (by omega) :=
    BitVec.append_assoc
  have read := congrArg
    (fun word : BitVec (((coefficientWidth + 1) + quotientWidth) + remainderWidth) =>
      word.extractLsb' remainderWidth ((coefficientWidth + 1) + quotientWidth)) assemble
  rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_cast] at read
  exact read.symm

private lemma original_prefix_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    ((frame state modulus count valid conserved active beforeEnd iteration).firstWord.extractLsb'
      (SignedDivisionPhase.nextWidth state modulus count + 1)
      (window state modulus count valid conserved active beforeEnd).above).toNat =
        (DivisionPackedStep.retainedPrefix state modulus count
          valid conserved active beforeEnd.le).toNat := by
  let payload := DivisionCapacity.work1Payload state modulus count
    valid conserved active beforeEnd.le
  have aboveEq : (window state modulus count valid conserved active beforeEnd).above =
      (state.coefficient.size + 1) + (DivisionProgress.current state count).written := by
    change state.coefficient.size + count + 1 = _
    rw [DivisionProgress.current_written]
    omega
  have remainderEq := DivisionThreshold.remainder_width_succ state modulus count
    valid conserved active beforeEnd
  change (((WordPacking.packWork1 payload).cast
    (DivisionCapacity.work1_width state modulus count
      valid conserved active beforeEnd.le)).extractLsb'
      (SignedDivisionPhase.nextWidth state modulus count + 1)
      (window state modulus count valid conserved active beforeEnd).above).toNat = _
  rw [BitVec.extractLsb'_cast]
  have read := congrArg BitVec.toNat (pack_prefix payload)
  have firstWidth := congrArg (fun start => ((WordPacking.packWork1 payload).extractLsb' start
    (window state modulus count valid conserved active beforeEnd).above).toNat) remainderEq
  have secondWidth := congrArg (fun length => ((WordPacking.packWork1 payload).extractLsb'
    (DivisionCapacity.remainderWidth state modulus count) length).toNat) aboveEq
  exact firstWidth.symm.trans (secondWidth.trans read)

private lemma full_word_toNat {width above below : Nat} (word : BitVec width)
    (complete : above + below = width) :
    word.toNat = (word.extractLsb' below above).toNat * 2 ^ below +
      (word.setWidth below).toNat := by
  have split : ((word.cast complete.symm).extractLsb' below above ++
      (word.cast complete.symm).extractLsb' 0 below) = word.cast complete.symm :=
    BitVec.extractLsb'_append_extractLsb'
  have read := congrArg BitVec.toNat split
  simp only [DivisionPackedStep.append_toNat, BitVec.extractLsb'_cast, BitVec.toNat_cast] at read
  have low : word.setWidth below = word.extractLsb' 0 below :=
    BitVec.setWidth_eq_extractLsb' (by omega)
  exact read.symm.trans
    (congrArg (fun value => (word.extractLsb' below above).toNat * 2 ^ below + value)
      (congrArg BitVec.toNat low).symm)

/-- Complete actual Work1 is the retained source prefix followed by the proved output word. -/
lemma native_instructionWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).firstWord =
        DivisionPackedStep.instructionWord state modulus count
          valid conserved active beforeEnd := by
  let selected := window state modulus count valid conserved active beforeEnd
  let original := frame state modulus count valid conserved active beforeEnd iteration
  let after := ArithmeticBlocks.remainderStep modulus.size original
  let output := SignQuotient.step modulus.size after
  have fields := RemainderPhaseExchange.native_fields state modulus count
    valid conserved active beforeEnd iteration
  have position := RemainderPhaseExchange.next_position state modulus count
    valid conserved active beforeEnd iteration
  have aboveEq : after.coefficientLength.toNat + after.quotientLength.toNat + 1 =
      selected.above := by
    change after.coefficientLength.toNat = state.coefficient.size ∧
      after.quotientLength.toNat = count ∧ _ at fields
    rw [fields.1, fields.2.1]
    rfl
  have prefixEq := native_prefix modulus.size after fields.2.2.2.2
    fields.2.2.1 fields.2.2.2.1 position.1
  change output.firstWord.extractLsb' (modulus.size + 3 - 1 -
      (after.coefficientLength.toNat + after.quotientLength.toNat + 1) + 1)
        (after.coefficientLength.toNat + after.quotientLength.toNat + 1) =
    after.firstWord.extractLsb' (modulus.size + 3 - 1 -
      (after.coefficientLength.toNat + after.quotientLength.toNat + 1) + 1)
        (after.coefficientLength.toNat + after.quotientLength.toNat + 1) at prefixEq
  rw [position.2, aboveEq] at prefixEq
  have retained := congrArg (fun value : Complement selected => value.1.1)
    (RemainderPhaseAction.native_complement state modulus count
      valid conserved active beforeEnd iteration)
  change (wordEquiv selected after.firstWord).1 =
    (wordEquiv selected original.firstWord).1 at retained
  have arithmeticPrefix := (wordEquiv_above selected after.firstWord).symm.trans
    (retained.trans (wordEquiv_above selected original.firstWord))
  have readWidth := RemainderPhaseExchange.read_width state modulus count
    valid conserved active beforeEnd
  change selected.length + selected.below =
    SignedDivisionPhase.nextWidth state modulus count + 1 at readWidth
  rw [readWidth] at arithmeticPrefix
  have allPrefix := prefixEq.trans arithmeticPrefix
  have prefixNat := (congrArg BitVec.toNat allPrefix).trans
    (original_prefix_toNat state modulus count valid conserved active beforeEnd iteration)
  have low := RemainderPhaseExchange.native_word state modulus count
    valid conserved active beforeEnd iteration
  have complete : selected.above + (SignedDivisionPhase.nextWidth state modulus count + 1) =
      modulus.size + 3 := readWidth ▸ selected.complete
  apply BitVec.eq_of_toNat_eq
  calc
    output.firstWord.toNat = _ := full_word_toNat output.firstWord complete
    _ = (DivisionPackedStep.retainedPrefix state modulus count
          valid conserved active beforeEnd.le).toNat *
        2 ^ (SignedDivisionPhase.nextWidth state modulus count + 1) +
          (SignedDivisionPhase.instruction state modulus count
            valid conserved active beforeEnd).2.toNat := by
      rw [prefixNat]
      exact congrArg (fun value => (DivisionPackedStep.retainedPrefix state modulus count
        valid conserved active beforeEnd.le).toNat *
          2 ^ (SignedDivisionPhase.nextWidth state modulus count + 1) + value)
        (congrArg BitVec.toNat low)
    _ = _ := by
      unfold DivisionPackedStep.instructionWord
      rw [BitVec.toNat_cast, DivisionPackedStep.append_toNat]

/-- Actual native arithmetic and quotient exchange produce the next complete packed Work1 state. -/
lemma native_firstWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (SignQuotient.step modulus.size (ArithmeticBlocks.remainderStep modulus.size
      (frame state modulus count valid conserved active beforeEnd iteration))).firstWord =
      (WordPacking.packWork1 (DivisionCapacity.work1Payload state modulus (count + 1)
        valid conserved active (by omega))).cast
          (DivisionCapacity.work1_width state modulus (count + 1)
            valid conserved active (by omega)) :=
  (native_instructionWord state modulus count valid conserved active beforeEnd iteration).trans
    (DivisionPackedStep.instructionWord_eq_next state modulus count
      valid conserved active beforeEnd)

end

end QuantumAlg.MAU.Inversion.SharedEEA.RemainderPhasePacking
