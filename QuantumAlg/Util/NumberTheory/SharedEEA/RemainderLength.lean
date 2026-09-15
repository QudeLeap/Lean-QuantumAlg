/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Length.Refresh

/-!
# Actual remainder-length refresh after coefficient-length refresh

The source refreshes the divisor length after the coefficient length.
Both exchanged work words are read on their right-most `n + 2 - ℓ_t`
bits, using that newly updated coefficient-length register
[LYL+26, sec_EEA/sub_regshare.tex:311-313]. As with the coefficient
length, the old and new lengths are written by two serial XORs
[LYL+26, sec_circuit/sub_block_new.tex:209-219].

Exact suffix extraction reads the old divisor from the first exchanged
word and the new divisor from the second. The shared-word capacities
establish both bounds even when the new divisor is zero. The successive
update theorem uses the actual preceding finite coefficient-length
update to choose the suffix width. No external length correctness
premise or active-next-iteration premise is introduced.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.RemainderLength

variable {wordWidth coefficientWidth quotientWidth remainderWidth clockWidth : Nat}

/-- The actual right suffix of a bounded pair is exactly its remainder field. -/
theorem read_right_work2 (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (widths : coefficientWidth + remainderWidth = wordWidth) :
    ((WordPacking.packWork2 payload).cast widths).extractLsb' 0 remainderWidth =
      payload.remainderBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, WordPacking.packWork2,
    BitVec.getLsbD_append, Nat.zero_add, within, decide_true, Bool.true_and, if_true]

/-- The first-word suffix reads its remainder independently of the coefficient and quotient. -/
theorem read_right_work1
    (payload : WordPacking.Work1Payload coefficientWidth quotientWidth remainderWidth)
    (widths : (coefficientWidth + 1) + (quotientWidth + remainderWidth) = wordWidth) :
    ((WordPacking.packWork1 payload).cast widths).extractLsb' 0 remainderWidth =
      payload.remainderBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have withinTail : index < quotientWidth + remainderWidth := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, WordPacking.packWork1,
    BitVec.getLsbD_append, Nat.zero_add, withinTail, within, decide_true, Bool.true_and, if_true]

/-- The macro first-word suffix contains its complete actual remainder. -/
theorem first_remainder (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    ((PackingBoundary.firstWord state modulus valid conserved).extractLsb' 0
      (PackingBoundary.firstRemainderWidth state modulus)).toNat = state.remainder := by
  unfold PackingBoundary.firstWord
  rw [read_right_work1]
  rfl

private theorem previous_fits (state : IterationState) (valid : state.Admissible) :
    state.previousCoefficient < 2 ^ (state.coefficient.size + 1) :=
  (valid.previous_lt.trans (Nat.lt_size_self state.coefficient)).trans_le
    (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))

private def secondReadPayload (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    WordPacking.Work2Payload (state.coefficient.size + 1)
      (PackingBoundary.firstRemainderWidth state modulus) where
  coefficientBits := BitVec.ofNatLT state.previousCoefficient (previous_fits state valid)
  remainderBits := BitVec.ofNatLT state.divisor
    (valid.divisor_lt.trans (PackingBoundary.first_remainder_fits state modulus valid conserved))

/-- The macro second word can be read at that same right boundary without truncation. -/
theorem second_remainder (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    ((PackingBoundary.secondWord state modulus valid conserved).extractLsb' 0
      (PackingBoundary.firstRemainderWidth state modulus)).toNat = state.divisor := by
  have widths : (state.coefficient.size + 1) +
      PackingBoundary.firstRemainderWidth state modulus = modulus.size + 3 := by
    simpa only [Nat.zero_add] using PackingBoundary.first_width state modulus valid conserved
  have resegmented : PackingBoundary.secondWord state modulus valid conserved =
      (WordPacking.packWork2 (secondReadPayload state modulus valid conserved)).cast widths := by
    unfold PackingBoundary.secondWord
    exact PackingBoundary.work2_resegment _ _ _ widths rfl rfl
  rw [resegmented, read_right_work2]
  rfl

/-- The old divisor is read from the actual first word after the whole-word exchange. -/
theorem read_old_divisor (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    ((PackingBoundary.completedSecondWord state modulus valid conserved active).extractLsb' 0
      (PackingBoundary.firstRemainderWidth (IterationState.step state) modulus)).toNat =
        state.divisor := by
  rw [PackingBoundary.completed_second_eq_next_first state modulus valid conserved active]
  exact first_remainder (IterationState.step state) modulus
    (IterationState.step_admissible state valid active)
    ((IterationState.step_balance state).trans conserved)

/-- The new divisor is read from the actual second word, including the zero terminal divisor. -/
theorem read_new_divisor (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    ((PackingBoundary.completedFirstWord state modulus valid conserved).extractLsb' 0
      (PackingBoundary.firstRemainderWidth (IterationState.step state) modulus)).toNat =
        (IterationState.step state).divisor := by
  rw [PackingBoundary.completed_first_eq_next_second state modulus valid conserved active]
  exact second_remainder (IterationState.step state) modulus
    (IterationState.step_admissible state valid active)
    ((IterationState.step_balance state).trans conserved)

/-- Read both actual suffixes and execute the prescribed old-then-new length XOR writes. -/
def remainderUpdate (readWidth : Nat) (first second : BitVec wordWidth)
    (length : BitVec clockWidth) : BitVec clockWidth :=
  LengthRefresh.serialXor length
    (BitVec.ofNat clockWidth (first.extractLsb' 0 readWidth).toNat.size)
    (BitVec.ofNat clockWidth (second.extractLsb' 0 readWidth).toNat.size)

/-- Reversing the actual suffix reads restores every prior finite length-register value. -/
theorem remainderUpdate_reverse (readWidth : Nat) (first second : BitVec wordWidth)
    (length : BitVec clockWidth) :
    remainderUpdate readWidth second first
        (remainderUpdate readWidth first second length) = length :=
  LengthRefresh.serialXor_reverse length _ _

/-- The actual read-and-XOR operations produce the exact next finite divisor-length register. -/
theorem remainder_update_exact (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    remainderUpdate (PackingBoundary.firstRemainderWidth (IterationState.step state) modulus)
        (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size state.divisor.size) =
      BitVec.ofNat modulus.size.size (IterationState.step state).divisor.size := by
  unfold remainderUpdate
  rw [read_old_divisor state modulus valid conserved active,
    read_new_divisor state modulus valid conserved active]
  exact LengthRefresh.serialXor_old _ _

/-- The refreshed finite register decodes to the full new divisor length without truncation. -/
theorem remainder_update_toNat (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (remainderUpdate (PackingBoundary.firstRemainderWidth (IterationState.step state) modulus)
        (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size state.divisor.size)).toNat =
      (IterationState.step state).divisor.size := by
  rw [remainder_update_exact state modulus valid conserved active]
  exact LengthRefresh.encoded_length_toNat _ modulus
    (Capacity.iteration_fields_le (IterationState.step state) modulus
      (IterationState.step_admissible state valid active)
      ((IterationState.step_balance state).trans conserved)).2.1

/-- The real preceding coefficient-length update selects precisely the proved suffix region. -/
theorem successive_update_exact (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    let first := PackingBoundary.completedSecondWord state modulus valid conserved active
    let second := PackingBoundary.completedFirstWord state modulus valid conserved
    let coefficientLength := LengthRefresh.coefficientUpdate
      (CoefficientCapacity.work2CoefficientWidth state modulus) first second
      (BitVec.ofNat modulus.size.size state.coefficient.size)
    remainderUpdate (modulus.size + 2 - coefficientLength.toNat) first second
        (BitVec.ofNat modulus.size.size state.divisor.size) =
      BitVec.ofNat modulus.size.size (IterationState.step state).divisor.size := by
  dsimp only
  rw [LengthRefresh.coefficient_update_toNat state modulus valid conserved active]
  have region : modulus.size + 2 - (IterationState.step state).coefficient.size =
      PackingBoundary.firstRemainderWidth (IterationState.step state) modulus := by
    unfold PackingBoundary.firstRemainderWidth
    omega
  rw [region]
  exact remainder_update_exact state modulus valid conserved active

end QuantumAlg.NumberTheory.SharedEEA.RemainderLength
