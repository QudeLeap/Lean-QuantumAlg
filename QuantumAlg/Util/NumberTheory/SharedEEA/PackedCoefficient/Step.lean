/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PackedCoefficient.Window

/-!
# Complete packed-word coefficient microsteps

The signed coefficient instructions replace the left arithmetic window
and then rotate the entire second work word one position to the left
[LYL+26, sec_EEA/sub_regshare.tex:288-296]. The rotated representation keeps
the low fractional part at the other end of that same word
[LYL+26, sec_EEA/sub_regshare.tex:263-264].

This owner proves equality of the entire actual replaced word with the
next coefficient payload at the old rotation. It accounts for the updated
window, the unchanged wrapped fraction, the high zero coefficient bits,
and every divisor bit. The subsequent literal left rotation therefore
gives exactly the next packed coefficient-phase state. These are exact
finite-word identities; no phase flag, history register, or cost is erased.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PackedCoefficientStep

/-- The updated arithmetic window is the next coefficient divided by the actual old scale. -/
lemma next_window (state : IterationState) (count : Nat) (valid : state.Admissible) :
    (CoefficientWindow.current state (count + 1)).value / 2 ^ count =
      ((CoefficientWindow.instruction state count valid).2.setWidth
        (CoefficientWindow.width state)).toNat := by
  have assembled := CoefficientWindow.reassembled_next state count valid
  unfold CoefficientWindow.reassembled CoefficientWindow.fractionPart at assembled
  rw [CoefficientCapacity.current_scale] at assembled
  have lowBound := Nat.mod_lt (CoefficientWindow.current state count).value
    (Nat.two_pow_pos count)
  calc
    _ = ((CoefficientWindow.current state count).value % 2 ^ count +
        ((CoefficientWindow.instruction state count valid).2.setWidth
          (CoefficientWindow.width state)).toNat * 2 ^ count) / 2 ^ count :=
      congrArg (fun value => value / 2 ^ count) (assembled.symm.trans (Nat.add_comm _ _))
    _ = _ := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos count), Nat.div_eq_of_lt lowBound,
        Nat.zero_add]

/-- The physical update preserves the complete low fraction, including nonzero fractions. -/
lemma fraction_preserved (state : IterationState) (count : Nat)
    (valid : state.Admissible) :
    (CoefficientWindow.current state (count + 1)).value % 2 ^ count =
      (CoefficientWindow.current state count).value % 2 ^ count := by
  have assembled := CoefficientWindow.reassembled_next state count valid
  unfold CoefficientWindow.reassembled CoefficientWindow.fractionPart at assembled
  rw [CoefficientCapacity.current_scale] at assembled
  calc
    _ = (((CoefficientWindow.instruction state count valid).2.setWidth
          (CoefficientWindow.width state)).toNat * 2 ^ count +
        (CoefficientWindow.current state count).value % 2 ^ count) % 2 ^ count :=
      congrArg (fun value => value % 2 ^ count) assembled.symm
    _ = _ := by rw [Nat.mul_add_mod_self_right, Nat.mod_mod]

/-- Both actual coefficients have zero bits above the complete aligned arithmetic window. -/
lemma values_below_window (state : IterationState) (count : Nat)
    (valid : state.Admissible) :
    (CoefficientWindow.current state count).value <
        2 ^ (count + CoefficientWindow.width state) ∧
      (CoefficientWindow.current state (count + 1)).value <
        2 ^ (count + CoefficientWindow.width state) := by
  have oldBound := (CoefficientWindow.valueWord state count valid).isLt
  change CoefficientWindow.integerPart state count <
    2 ^ CoefficientWindow.width state at oldBound
  unfold CoefficientWindow.integerPart at oldBound
  rw [CoefficientCapacity.current_scale] at oldBound
  have newBound : (CoefficientWindow.current state (count + 1)).value / 2 ^ count <
      2 ^ CoefficientWindow.width state := by
    rw [next_window state count valid]
    exact ((CoefficientWindow.instruction state count valid).2.setWidth
      (CoefficientWindow.width state)).isLt
  have oldValue := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos count)).mp oldBound
  have newValue := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos count)).mp newBound
  constructor
  · simpa only [Nat.pow_add, Nat.mul_comm] using oldValue
  · simpa only [Nat.pow_add, Nat.mul_comm] using newValue

/-- Every coefficient bit outside the actual aligned window is unchanged by the microstep. -/
lemma coefficient_outside (state : IterationState) (count : Nat)
    (valid : state.Admissible) (index : Nat)
    (outside : index < count ∨ count + CoefficientWindow.width state ≤ index) :
    (CoefficientWindow.current state (count + 1)).value.testBit index =
      (CoefficientWindow.current state count).value.testBit index := by
  rcases outside with below | above
  · have same := congrArg (fun value => value.testBit index)
      (fraction_preserved state count valid)
    simpa only [Nat.testBit_mod_two_pow, below, decide_true, Bool.true_and] using same
  · have bounds := values_below_window state count valid
    have powerBound := Nat.pow_le_pow_right (Nat.zero_lt_two) above
    calc
      _ = false := Nat.testBit_lt_two_pow (bounds.2.trans_le powerBound)
      _ = _ := (Nat.testBit_lt_two_pow (bounds.1.trans_le powerBound)).symm

private lemma rotated_outside (count windowWidth coefficientWidth remainderWidth index : Nat)
    (fits : count + windowWidth ≤ coefficientWidth)
    (outside : windowWidth ≤ index) (within : index < coefficientWidth + remainderWidth) :
    (count + index) % (coefficientWidth + remainderWidth) < count ∨
      count + windowWidth ≤ (count + index) % (coefficientWidth + remainderWidth) := by
  by_cases beforeWrap : count + index < coefficientWidth + remainderWidth
  · right
    rw [Nat.mod_eq_of_lt beforeWrap]
    omega
  · left
    have restBound : count + index - (coefficientWidth + remainderWidth) <
        coefficientWidth + remainderWidth := by omega
    have splitPosition : count + index = coefficientWidth + remainderWidth +
        (count + index - (coefficientWidth + remainderWidth)) := by omega
    have reduced : (count + index) % (coefficientWidth + remainderWidth) =
        count + index - (coefficientWidth + remainderWidth) := by
      calc
        _ = (coefficientWidth + remainderWidth +
            (count + index - (coefficientWidth + remainderWidth))) %
              (coefficientWidth + remainderWidth) :=
          congrArg (fun value => value % (coefficientWidth + remainderWidth)) splitPosition
        _ = _ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt restBound]
    rw [reduced]
    omega

/-- Repacking the next payload at the old shift preserves every outside physical bit. -/
lemma repacked_outside (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size)
    (index : Nat) (outside : CoefficientWindow.width state ≤ index)
    (inWord : index <
      CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size) :
    (WordRotation.packRotatedWork2 count
        (CoefficientCapacity.work2Payload state modulus (count + 1)
          valid conserved active)).getMsbD index =
      (PackedCoefficientWindow.word state modulus count valid conserved active).getMsbD index := by
  simp only [PackedCoefficientWindow.word, WordRotation.packRotatedWork2_bit, inWord,
    decide_true, Bool.true_and]
  by_cases inDivisor : CoefficientCapacity.work2CoefficientWidth state modulus ≤
      (count + index) %
        (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size)
  · simp only [if_pos inDivisor, CoefficientCapacity.work2Payload]
  · simp only [if_neg inDivisor]
    change (CoefficientWindow.current state (count + 1)).value.testBit
        ((count + index) %
          (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size)) =
      (CoefficientWindow.current state count).value.testBit
        ((count + index) %
          (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size))
    exact coefficient_outside state count valid _ (rotated_outside count
      (CoefficientWindow.width state) (CoefficientCapacity.work2CoefficientWidth state modulus)
      state.divisor.size index
      (CoefficientWindow.arithmetic_window_fits state modulus count valid conserved active within)
      outside inWord)

/-- The next payload at the old rotation exposes exactly the window actually written. -/
lemma repacked_read (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    PhysicalWindow.read (CoefficientWindow.width state)
        (WordRotation.packRotatedWork2 count
          (CoefficientCapacity.work2Payload state modulus (count + 1) valid conserved active)) =
      (CoefficientWindow.instruction state count valid).2.setWidth
        (CoefficientWindow.width state) := by
  rw [PhysicalWindow.read_rotated count _
    (CoefficientWindow.arithmetic_window_fits state modulus count valid conserved active within)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change ((CoefficientWindow.current state (count + 1)).value / 2 ^ count) %
      2 ^ CoefficientWindow.width state =
    ((CoefficientWindow.instruction state count valid).2.setWidth
      (CoefficientWindow.width state)).toNat
  rw [next_window state count valid]
  exact Nat.mod_eq_of_lt ((CoefficientWindow.instruction state count valid).2.setWidth
    (CoefficientWindow.width state)).isLt

/-- Actual physical window replacement equals the entire next payload at the old rotation. -/
lemma updated_eq_repacked (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    PackedCoefficientWindow.updatedWord state modulus count valid conserved active within =
      WordRotation.packRotatedWork2 count
        (CoefficientCapacity.work2Payload state modulus (count + 1) valid conserved active) := by
  apply BitVec.eq_of_getMsbD_eq
  intro index inWord
  by_cases inWindow : index < CoefficientWindow.width state
  · have fits := PackedCoefficientWindow.window_fits state modulus count
      valid conserved active within
    calc
      _ = (PhysicalWindow.read (CoefficientWindow.width state)
          (PackedCoefficientWindow.updatedWord state modulus count
            valid conserved active within)).getLsbD index :=
        (PhysicalWindow.read_bit _ fits index inWindow).symm
      _ = ((CoefficientWindow.instruction state count valid).2.setWidth
          (CoefficientWindow.width state)).getLsbD index :=
        congrArg (fun value => value.getLsbD index)
          (PackedCoefficientWindow.updated_read state modulus count valid conserved active within)
      _ = (PhysicalWindow.read (CoefficientWindow.width state)
          (WordRotation.packRotatedWork2 count
            (CoefficientCapacity.work2Payload state modulus (count + 1)
              valid conserved active))).getLsbD index :=
        congrArg (fun value => value.getLsbD index)
          (repacked_read state modulus count valid conserved active within).symm
      _ = _ := PhysicalWindow.read_bit _ fits index inWindow
  · have outside : CoefficientWindow.width state ≤ index := by omega
    exact (PackedCoefficientWindow.updated_outside state modulus count valid conserved active
      within index outside inWord).trans
        (repacked_outside state modulus count valid conserved active
          within index outside inWord).symm

/-- The actual signed replacement followed by the source's one-position shift is the next word. -/
lemma step_eq_next_word (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    (PackedCoefficientWindow.updatedWord state modulus count
        valid conserved active within).rotateLeft 1 =
      PackedCoefficientWindow.word state modulus (count + 1) valid conserved active := by
  rw [updated_eq_repacked state modulus count valid conserved active within]
  exact WordRotation.packRotatedWork2_shift count _

/-- Undoing that last actual shift recovers the complete updated word before rotation. -/
lemma unshift_next_word (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) :
    (PackedCoefficientWindow.word state modulus (count + 1) valid conserved active).rotateRight 1 =
      PackedCoefficientWindow.updatedWord state modulus count valid conserved active within := by
  rw [← step_eq_next_word state modulus count valid conserved active within]
  exact WordRotation.rotateRight_rotateLeft _ 1

end QuantumAlg.NumberTheory.SharedEEA.PackedCoefficientStep
