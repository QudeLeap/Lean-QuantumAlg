/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Threshold

/-!
# Exact divisor extraction from the actually rotated second shared word

The source rotates the complete Work2 payload and excludes the wrapped
low suffix from remainder arithmetic
[LYL+26, sec_EEA/sub_regshare.tex:263-278,279-287]. The selected upper
window must contain the divisor without including old coefficient bits.

The generic finite-word identity below checks every physical bit. Its
application to the actual division position derives the required geometry
from the already proved threshold capacity and derives coefficient
separation from the reachable ordering `previousCoefficient < coefficient`.
The original wrapped fraction may be arbitrary. No source operand is
replaced by a separately initialized divisor, and no capacity premise is
added to the original input domain.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionWindow

private lemma unrotated_low {coefficientWidth remainderWidth length : Nat}
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (within : length ≤ coefficientWidth + remainderWidth)
    (separated : payload.coefficientBits.toNat <
      2 ^ (coefficientWidth + remainderWidth - length)) :
    (WordPacking.packWork2 payload).setWidth length = payload.remainderBits.setWidth length := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit bitWithin
  simp only [BitVec.getLsbD_setWidth, bitWithin, decide_true, Bool.true_and,
    WordPacking.packWork2, BitVec.getLsbD_append]
  by_cases inRemainder : bit < remainderWidth
  · rw [if_pos inRemainder]
  · rw [if_neg inRemainder, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD]
    have coefficientIndex : bit - remainderWidth < coefficientWidth := by omega
    have exponent : coefficientWidth + remainderWidth - length ≤
        coefficientWidth - 1 - (bit - remainderWidth) := by omega
    have upperZero : payload.coefficientBits.getLsbD
        (coefficientWidth - 1 - (bit - remainderWidth)) = false :=
      Nat.testBit_lt_two_pow
        (separated.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two exponent))
    rw [decide_eq_true coefficientIndex, Bool.true_and, upperZero]
    exact (BitVec.getLsbD_of_ge payload.remainderBits bit (by omega)).symm

/-- Reading above the actual wrapped suffix recovers the corresponding unrotated low bits. -/
lemma rotated_read {coefficientWidth remainderWidth length : Nat}
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) (shift : Nat)
    (within : length + shift ≤ coefficientWidth + remainderWidth)
    (separated : payload.coefficientBits.toNat <
      2 ^ (coefficientWidth + remainderWidth - length)) :
    (WordRotation.packRotatedWork2 shift payload).extractLsb' shift length =
      payload.remainderBits.setWidth length := by
  have low := unrotated_low payload (by omega : length ≤ coefficientWidth + remainderWidth)
    separated
  calc
    _ = (WordPacking.packWork2 payload).setWidth length := by
      apply BitVec.eq_of_getLsbD_eq
      intro bit bitWithin
      have shiftWithin : shift < coefficientWidth + remainderWidth := by omega
      have sourceWithin : shift + bit < coefficientWidth + remainderWidth := by omega
      have afterShift : ¬shift + bit < shift := by omega
      simp only [WordRotation.packRotatedWork2, BitVec.getLsbD_extractLsb',
        bitWithin, decide_true, Bool.true_and, BitVec.getLsbD_rotateLeft,
        Nat.mod_eq_of_lt shiftWithin, afterShift, decide_false, cond_false,
        sourceWithin, Nat.add_sub_cancel_left, BitVec.getLsbD_setWidth]
    _ = _ := low

/-- The physical shift after the source's actual pre-subtraction right rotation. -/
def shift (state : IterationState) (count : Nat) : Nat :=
  (Alignment.align state.remainder state.divisor).places - (count + 1)

/-- The coefficient, explicit separator, and already written quotient precede the window. -/
def above (state : IterationState) (count : Nat) : Nat :=
  state.coefficient.size + 1 + count

/-- The high arithmetic region excludes the complete unchanged low shift suffix. -/
def length (state : IterationState) (modulus count : Nat) : Nat :=
  modulus.size + 3 - above state count - shift state count

/-- The actual shifted threshold has exactly the divisor's width plus the remaining shift. -/
lemma threshold_size (state : IterationState) (count : Nat)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (DivisionThreshold.threshold state count).size = state.divisor.size + shift state count := by
  rw [DivisionThreshold.threshold_eq state count active beforeEnd,
    Nat.mul_comm, ← Nat.shiftLeft_eq_mul_pow]
  exact Nat.size_shiftLeft (Nat.ne_of_gt active) _

/-- The entire selected physical geometry is valid at every actual phase-two position. -/
lemma window_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    above state count + shift state count ≤ modulus.size + 3 := by
  have capacity := DivisionThreshold.threshold_size state modulus count
    valid conserved active beforeEnd
  rw [threshold_size state count active beforeEnd] at capacity
  unfold above
  omega

/-- The actual aligned divisor fits the selected finite operand without modular truncation. -/
lemma divisor_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    state.divisor.size ≤ length state modulus count := by
  have capacity := DivisionThreshold.threshold_size state modulus count
    valid conserved active beforeEnd
  rw [threshold_size state count active beforeEnd] at capacity
  unfold length above
  omega

/-- Reading the actual rotated packed Work2 at the source boundaries returns exactly the divisor. -/
lemma source_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    ((WordRotation.packRotatedWork2 (shift state count)
      (DivisionCapacity.work2Payload state modulus valid conserved)).extractLsb'
        (shift state count) (length state modulus count)).toNat = state.divisor := by
  let payload := DivisionCapacity.work2Payload state modulus valid conserved
  have complete := DivisionCapacity.work2_width state modulus valid conserved
  have fits := window_fits state modulus count valid conserved active beforeEnd
  have geometry : length state modulus count + shift state count ≤
      CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size := by
    rw [complete]
    unfold length
    omega
  have separated : payload.coefficientBits.toNat <
      2 ^ (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size -
        length state modulus count) := by
    change state.previousCoefficient < _
    have ordered : state.previousCoefficient < 2 ^ state.coefficient.size :=
      valid.previous_lt.trans (Nat.lt_size_self _)
    apply ordered.trans_le
    apply Nat.pow_le_pow_right Nat.zero_lt_two
    rw [complete]
    dsimp only [above] at fits
    unfold length above
    omega
  have actual := rotated_read payload (shift state count) geometry separated
  have decoded := congrArg BitVec.toNat actual
  have unchanged : (payload.remainderBits.setWidth (length state modulus count)).toNat =
      payload.remainderBits.toNat :=
    BitVec.toNat_setWidth_of_le (divisor_fits state modulus count valid conserved active beforeEnd)
  exact decoded.trans unchanged

end QuantumAlg.NumberTheory.SharedEEA.DivisionWindow
