/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Window

/-!
# Complete physical alignment window through the first rejecting comparison

The first phase doubles the actual scale and rotates the entire second
word before comparing the remainder with that shifted divisor
[LYL+26, sec_EEA/sub_regshare.tex:275-278]. The final rejecting comparison
uses one bit above the highest division threshold. Original macro capacity
still fits that full divisor and the coefficient's explicit separator.

The quotient size below bounds and characterizes the already executed
alignment trajectory. It is not a precomputed initial counter or a loop
condition replacing comparison. The exact rotated-word read retains all
old coefficient bits and covers the full first-phase range, including its
last rejecting threshold and the smallest original positive input.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.AlignmentWindow

/-- The actual alignment's highest comparison retains one bit beyond the division threshold. -/
theorem complete_capacity (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    state.coefficient.size + 1 + state.divisor.size + state.quotient.size ≤ modulus.size + 3 := by
  have places := Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  change (Alignment.align state.remainder state.divisor).places = state.quotient.size at places
  have positive : 0 < (Alignment.align state.remainder state.divisor).places := by
    rw [places]
    exact Nat.size_pos.mpr (IterationState.quotient_pos state valid.divisor_lt active)
  have highest := DivisionThreshold.threshold_size state modulus 0
    valid conserved active positive
  rw [DivisionWindow.threshold_size state 0 active positive] at highest
  change state.coefficient.size + 0 +
    (state.divisor.size + ((Alignment.align state.remainder state.divisor).places - (0 + 1))) ≤
      modulus.size + 1 at highest
  rw [places] at highest
  rw [places] at positive
  omega

/-- The actual shared window excludes the coefficient separator and retained low shift suffix. -/
def length (state : IterationState) (modulus shift : Nat) : Nat :=
  modulus.size + 3 - (state.coefficient.size + 1) - shift

/-- All actual first-phase positions fit the original work word without caller-supplied geometry. -/
theorem window_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    state.coefficient.size + 1 + shift ≤ modulus.size + 3 := by
  have complete := complete_capacity state modulus valid conserved active
  omega

/-- The complete divisor fits the actual window even at the final rejecting comparison. -/
theorem divisor_fits (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    state.divisor.size ≤ length state modulus shift := by
  have complete := complete_capacity state modulus valid conserved active
  unfold length
  omega

/-- The real rotated second-word region reads exactly the complete divisor, with no truncation. -/
theorem source_toNat (state : IterationState) (modulus shift : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : shift ≤ state.quotient.size) :
    ((WordRotation.packRotatedWork2 shift
      (DivisionCapacity.work2Payload state modulus valid conserved)).extractLsb'
        shift (length state modulus shift)).toNat = state.divisor := by
  let payload := DivisionCapacity.work2Payload state modulus valid conserved
  have complete := DivisionCapacity.work2_width state modulus valid conserved
  have fits := window_fits state modulus shift valid conserved active within
  have geometry : length state modulus shift + shift ≤
      CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size := by
    rw [complete]
    unfold length
    omega
  have separated : payload.coefficientBits.toNat <
      2 ^ (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size -
        length state modulus shift) := by
    change state.previousCoefficient < _
    have ordered : state.previousCoefficient < 2 ^ state.coefficient.size :=
      valid.previous_lt.trans (Nat.lt_size_self _)
    apply ordered.trans_le
    apply Nat.pow_le_pow_right Nat.zero_lt_two
    rw [complete]
    unfold length
    omega
  have actual := DivisionWindow.rotated_read payload shift geometry separated
  have decoded := congrArg BitVec.toNat actual
  have unchanged : (payload.remainderBits.setWidth (length state modulus shift)).toNat =
      payload.remainderBits.toNat :=
    BitVec.toNat_setWidth_of_le (divisor_fits state modulus shift valid conserved active within)
  exact decoded.trans unchanged

end QuantumAlg.NumberTheory.SharedEEA.AlignmentWindow
