/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Capacity

/-!
# Exact boundary refresh after shared-word exchange

The source swaps the complete work words after quotient consumption and
deshifting, then refreshes the coefficient and divisor lengths
[LYL+26, sec_EEA/sub_regshare.tex:309-315]. The first word has an explicit
zero separator and a big-endian quotient region; the second word has only
the two opposite-endian endpoint fields
[LYL+26, sec_EEA/sub_regshare.tex:16-20].

Moving a logical boundary inside the intervening zero region does not
move any physical bit. The proofs below establish this from literal
concatenation, including the cleared quotient and separator positions.
The actual completed coefficient payloads therefore become precisely the
next macro iteration's two payloads under the source's whole-word swap.
Reachable cross-sum capacities supply every field bound. A zero terminal
divisor is included; no active-next-iteration assumption is used.

These are finite-word identities at the unrotated exchange boundary.
The existing fourth-phase owner supplies the actual deshifting law;
history recovery and a complete physical circuit remain separate duties.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PackingBoundary

variable {coefficientWidth quotientWidth remainderWidth : Nat}
variable {otherCoefficientWidth otherRemainderWidth wordWidth : Nat}

private lemma upper_bit_zero {width : Nat} (word : BitVec width) (index : Nat)
    (above : width ≤ index) : word.toNat.testBit index = false :=
  Nat.testBit_lt_two_pow (word.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two above))

/-- Every two-field word bit is determined by the two actual endpoint values. -/
lemma work2_bit (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (index : Nat) (within : index < coefficientWidth + remainderWidth) :
    (WordPacking.packWork2 payload).getMsbD index =
      (payload.coefficientBits.toNat.testBit index ||
        payload.remainderBits.toNat.testBit (coefficientWidth + remainderWidth - 1 - index)) := by
  by_cases inCoefficient : index < coefficientWidth
  · rw [WordPacking.packWork2_coefficient_bit payload index inCoefficient]
    change payload.coefficientBits.toNat.testBit index = _
    rw [upper_bit_zero payload.remainderBits _ (by omega), Bool.or_false]
  · have afterCoefficient : coefficientWidth ≤ index := by omega
    have sourceWithin : index - coefficientWidth < remainderWidth := by omega
    have physicalIndex : coefficientWidth + (index - coefficientWidth) = index := by omega
    have sourceIndex : remainderWidth - 1 - (index - coefficientWidth) =
        coefficientWidth + remainderWidth - 1 - index := by omega
    have entry := WordPacking.packWork2_remainder_bit payload (index - coefficientWidth)
    rw [physicalIndex] at entry
    rw [entry, BitVec.getMsbD_eq_getLsbD]
    simp only [sourceWithin, decide_true, Bool.true_and]
    change payload.remainderBits.toNat.testBit
        (remainderWidth - 1 - (index - coefficientWidth)) = _
    rw [sourceIndex, upper_bit_zero payload.coefficientBits index afterCoefficient, Bool.false_or]

/-- Once the quotient is actually zero, its entire region and the separator are zero padding. -/
lemma work1_zero_quotient_bit
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth)
    (empty : payload.quotientBits.toNat = 0) (index : Nat)
    (within : index < (coefficientWidth + 1) + (quotientWidth + remainderWidth)) :
    (WordPacking.packWork1 payload).getMsbD index =
      (payload.coefficientBits.toNat.testBit index ||
        payload.remainderBits.toNat.testBit
          ((coefficientWidth + 1) + (quotientWidth + remainderWidth) - 1 - index)) := by
  by_cases inCoefficient : index < coefficientWidth
  · rw [WordPacking.packWork1_coefficient_bit payload index inCoefficient]
    change payload.coefficientBits.toNat.testBit index = _
    rw [upper_bit_zero payload.remainderBits _ (by omega), Bool.or_false]
  · have afterCoefficient : coefficientWidth ≤ index := by omega
    rw [upper_bit_zero payload.coefficientBits index afterCoefficient, Bool.false_or]
    by_cases separator : index = coefficientWidth
    · subst index
      rw [WordPacking.packWork1_separator]
      exact (upper_bit_zero payload.remainderBits _ (by omega)).symm
    · by_cases inQuotient : index < coefficientWidth + 1 + quotientWidth
      · have quotientIndex : coefficientWidth + 1 +
            (index - (coefficientWidth + 1)) = index := by omega
        have quotientWithin : index - (coefficientWidth + 1) < quotientWidth := by omega
        have entry := WordPacking.packWork1_quotient_bit payload
          (index - (coefficientWidth + 1)) quotientWithin
        rw [quotientIndex] at entry
        rw [entry, BitVec.getMsbD_eq_getLsbD]
        change (decide (index - (coefficientWidth + 1) < quotientWidth) &&
            payload.quotientBits.toNat.testBit
              (quotientWidth - 1 - (index - (coefficientWidth + 1)))) = _
        rw [empty, Nat.zero_testBit, Bool.and_false]
        exact (upper_bit_zero payload.remainderBits _ (by omega)).symm
      · have remainderIndex : coefficientWidth + 1 + quotientWidth +
            (index - (coefficientWidth + 1 + quotientWidth)) = index := by omega
        have sourceWithin : index - (coefficientWidth + 1 + quotientWidth) <
            remainderWidth := by omega
        have sourceIndex : remainderWidth - 1 -
            (index - (coefficientWidth + 1 + quotientWidth)) =
              (coefficientWidth + 1) + (quotientWidth + remainderWidth) - 1 - index := by omega
        have entry := WordPacking.packWork1_remainder_bit payload
          (index - (coefficientWidth + 1 + quotientWidth))
        rw [remainderIndex] at entry
        rw [entry, BitVec.getMsbD_eq_getLsbD]
        simp only [sourceWithin, decide_true, Bool.true_and]
        change payload.remainderBits.toNat.testBit
            (remainderWidth - 1 - (index - (coefficientWidth + 1 + quotientWidth))) = _
        rw [sourceIndex]

/-- Redistributing zero padding between two bounded endpoint fields preserves the entire word. -/
lemma work2_resegment
    (left : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (right : WordPacking.Work2Payload otherCoefficientWidth otherRemainderWidth)
    (leftWidth : coefficientWidth + remainderWidth = wordWidth)
    (rightWidth : otherCoefficientWidth + otherRemainderWidth = wordWidth)
    (coefficient : left.coefficientBits.toNat = right.coefficientBits.toNat)
    (remainder : left.remainderBits.toNat = right.remainderBits.toNat) :
    (WordPacking.packWork2 left).cast leftWidth =
      (WordPacking.packWork2 right).cast rightWidth := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [BitVec.getMsbD_cast, BitVec.getMsbD_cast,
    work2_bit left index (by omega), work2_bit right index (by omega),
    leftWidth, rightWidth, coefficient, remainder]

/-- A genuinely cleared first-word quotient can be absorbed into either pair boundary exactly. -/
lemma work1_resegment
    (left : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth)
    (right : WordPacking.Work2Payload otherCoefficientWidth otherRemainderWidth)
    (leftWidth : (coefficientWidth + 1) + (quotientWidth + remainderWidth) = wordWidth)
    (rightWidth : otherCoefficientWidth + otherRemainderWidth = wordWidth)
    (empty : left.quotientBits.toNat = 0)
    (coefficient : left.coefficientBits.toNat = right.coefficientBits.toNat)
    (remainder : left.remainderBits.toNat = right.remainderBits.toNat) :
    (WordPacking.packWork1 left).cast leftWidth =
      (WordPacking.packWork2 right).cast rightWidth := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  rw [BitVec.getMsbD_cast, BitVec.getMsbD_cast,
    work1_zero_quotient_bit left empty index (by omega), work2_bit right index (by omega),
    leftWidth, rightWidth, coefficient, remainder]

/-- At a macro boundary, the first word has no effective quotient and retains its separator. -/
def firstRemainderWidth (state : IterationState) (modulus : Nat) : Nat :=
  modulus.size + 3 - (state.coefficient.size + 1)

/-- Reachable macro capacity leaves precisely the remainder region after coefficient and zero. -/
lemma first_width (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (state.coefficient.size + 1) + (0 + firstRemainderWidth state modulus) =
      modulus.size + 3 := by
  have room := (Capacity.iteration_word_capacity state modulus valid conserved).1
  unfold firstRemainderWidth
  omega

/-- The actual macro remainder fits the first word, including at the final zero-divisor boundary. -/
lemma first_remainder_fits (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.remainder < 2 ^ firstRemainderWidth state modulus := by
  apply Nat.size_le.mp
  have room := (Capacity.iteration_word_capacity state modulus valid conserved).1
  unfold firstRemainderWidth
  omega

/-- Encode the exact first-word fields at a macro boundary without truncating the remainder. -/
def firstPayload (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    WordPacking.Work1Payload state.coefficient.size 0 (firstRemainderWidth state modulus) where
  coefficientBits := BitVec.ofNatLT state.coefficient (Nat.lt_size_self _)
  quotientBits := 0
  remainderBits := BitVec.ofNatLT state.remainder
    (first_remainder_fits state modulus valid conserved)

/-- The first actual shared word at a reachable macro boundary. -/
def firstWord (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) : BitVec (modulus.size + 3) :=
  (WordPacking.packWork1 (firstPayload state modulus valid conserved)).cast
    (first_width state modulus valid conserved)

/-- The second actual shared word at a reachable macro boundary, including zero divisors. -/
def secondWord (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) : BitVec (modulus.size + 3) :=
  (WordPacking.packWork2 (DivisionCapacity.work2Payload state modulus valid conserved)).cast
    (DivisionCapacity.work2_width state modulus valid conserved)

/-- The actual first payload after every effective coefficient-phase quotient digit is consumed. -/
def completedFirstWord (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) : BitVec (modulus.size + 3) :=
  (WordPacking.packWork1
    (CoefficientCapacity.work1Payload state modulus state.quotient.size valid conserved)).cast
      (CoefficientCapacity.work1_width state modulus state.quotient.size valid conserved)

/-- The completed second payload after its retained circular shift has actually been undone. -/
def completedSecondWord (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) : BitVec (modulus.size + 3) :=
  (WordPacking.packWork2
    (CoefficientCapacity.work2Payload state modulus state.quotient.size
      valid conserved active)).cast
        (CoefficientCapacity.work2_width state modulus valid conserved)

/-- The completed first word is exactly the next second word under its refreshed boundary. -/
lemma completed_first_eq_next_second (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    completedFirstWord state modulus valid conserved =
      secondWord (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) := by
  unfold completedFirstWord secondWord
  apply work1_resegment
  · change (CoefficientPhase.finish state.coefficient (CoefficientPhase.start state)).remaining = 0
    exact CoefficientPhase.finish_remaining _ _
  · rfl
  · rfl

/-- The completed second word supplies the next coefficient and its genuine zero separator. -/
lemma completed_second_eq_next_first (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    completedSecondWord state modulus valid conserved active =
      firstWord (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) := by
  symm
  unfold completedSecondWord firstWord
  apply work1_resegment
  · rfl
  · exact (CoefficientPhase.finish_start_coefficient state).symm
  · rfl

/-- The literal whole-word exchange has precisely the next macro state's two physical words. -/
lemma completed_exchange (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (completedFirstWord state modulus valid conserved,
        completedSecondWord state modulus valid conserved active).swap =
      (firstWord (IterationState.step state) modulus
          (IterationState.step_admissible state valid active)
          ((IterationState.step_balance state).trans conserved),
        secondWord (IterationState.step state) modulus
          (IterationState.step_admissible state valid active)
          ((IterationState.step_balance state).trans conserved)) :=
  Prod.ext (completed_second_eq_next_first state modulus valid conserved active)
    (completed_first_eq_next_second state modulus valid conserved active)

/-- The smallest original domain input reaches a zero-divisor exchange without excluding it. -/
lemma smallest_terminal_exchange :
    let state := IterationState.initial 2 (foldInput 2 1).2
    let valid := folded_initial_admissible 2 1 (by decide) (by decide)
    let conserved := IterationState.initial_balance 2 (foldInput 2 1).2
    let active : 0 < state.divisor := by decide
    (IterationState.step state).divisor = 0 ∧
      (completedSecondWord state 2 valid conserved active).toNat = 9 ∧
      (completedFirstWord state 2 valid conserved).toNat = 16 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.PackingBoundary
