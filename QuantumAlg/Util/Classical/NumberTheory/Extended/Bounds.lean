/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.NumberTheory.Extended

/-!
# A polynomial bound for the original execution coefficient width

The original finite supremum ranges over the same actual active states and
finished state. Both remainders stay below the input capacity, so each actual
coefficient update multiplies the largest magnitude by at most that capacity.
The original linear fuel then bounds both coefficient suprema, without
enumerating any fixed-width inputs or replacing the execution workspace.
-/

namespace QuantumAlg.ClassicalAlgorithms.NumberTheory.XGCD

private lemma update_magnitude_le (left right : Int) (quotient bound : Nat)
    (leftBound : left.natAbs ≤ bound) (rightBound : right.natAbs ≤ bound) :
    (left - (quotient : Int) * right).natAbs ≤ (quotient + 1) * bound := by
  calc
    _ ≤ left.natAbs + ((quotient : Int) * right).natAbs := Int.natAbs_sub_le _ _
    _ = left.natAbs + quotient * right.natAbs := by rw [Int.natAbs_mul]; rfl
    _ ≤ bound + quotient * bound :=
      Nat.add_le_add leftBound (Nat.mul_le_mul_left quotient rightBound)
    _ = _ := by ring

/-- One original coefficient update grows by at most its quotient plus one. -/
lemma xgcdStep_coefficientMagnitude_le (state : State) :
    (step state).coefficientMagnitude ≤ (state.quotient + 1) * state.coefficientMagnitude := by
  have retained : state.coefficientMagnitude ≤
      (state.quotient + 1) * state.coefficientMagnitude :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  exact max_le
    (max_le
      (update_magnitude_le _ _ _ _
        (State.secondLeftCoefficient_natAbs_le_coefficientMagnitude state)
        (State.firstLeftCoefficient_natAbs_le_coefficientMagnitude state))
      (update_magnitude_le _ _ _ _
        (State.secondRightCoefficient_natAbs_le_coefficientMagnitude state)
        (State.firstRightCoefficient_natAbs_le_coefficientMagnitude state)))
    (max_le
      ((State.firstLeftCoefficient_natAbs_le_coefficientMagnitude state).trans retained)
      ((State.firstRightCoefficient_natAbs_le_coefficientMagnitude state).trans retained))

private lemma execution_magnitude_le (width fuel : Nat) (state : State)
    (firstRange : state.first < 2 ^ width) (secondRange : state.second < 2 ^ width) :
    stateListCoefficientMagnitude (path fuel state ++ [run fuel state]) ≤
      (2 ^ width) ^ fuel * state.coefficientMagnitude := by
  induction fuel generalizing state with
  | zero => simp [path, run, stateListCoefficientMagnitude]
  | succ fuel inductionHypothesis =>
      have selfBound : state.coefficientMagnitude ≤
          (2 ^ width) ^ (fuel + 1) * state.coefficientMagnitude :=
        Nat.le_mul_of_pos_left _ (pow_pos (pow_pos (by decide) _) _)
      by_cases finished : state.first = 0
      · simpa [path, run, finished, stateListCoefficientMagnitude] using selfBound
      · have firstStepRange : (step state).first < 2 ^ width :=
          (Nat.mod_le _ _).trans_lt secondRange
        have secondStepRange : (step state).second < 2 ^ width := firstRange
        have quotientBound : state.quotient + 1 ≤ 2 ^ width := by
          have bounded := (Nat.div_le_self state.second state.first).trans_lt secondRange
          exact Nat.succ_le_of_lt bounded
        have growth : (step state).coefficientMagnitude ≤
            2 ^ width * state.coefficientMagnitude :=
          (xgcdStep_coefficientMagnitude_le state).trans
            (Nat.mul_le_mul_right _ quotientBound)
        have tailBound :=
          (inductionHypothesis (step state) firstStepRange secondStepRange).trans
            (Nat.mul_le_mul_left _ growth)
        have product : (2 ^ width) ^ fuel * (2 ^ width * state.coefficientMagnitude) =
            (2 ^ width) ^ (fuel + 1) * state.coefficientMagnitude := by
          rw [pow_succ]
          ring
        rw [path, if_neg finished, run, if_neg finished]
        change max state.coefficientMagnitude
          (stateListCoefficientMagnitude (path fuel (step state) ++ [run fuel (step state)])) ≤ _
        exact max_le selfBound (tailBound.trans_eq product)

private lemma executionStates_magnitude_le {width : Nat} (input : Input width) :
    stateListCoefficientMagnitude (executionStates input) ≤ 2 ^ (width * (2 * width + 1)) := by
  have bounded := execution_magnitude_le width (Euclid.gcdFuel width) (initialState input)
    input.left.isLt input.right.isLt
  simpa only [executionStates, trace, finalState, initialState, State.coefficientMagnitude,
    Int.natAbs_one, Int.natAbs_zero, Nat.max_zero, Nat.zero_max, Nat.max_self, mul_one,
    Euclid.gcdFuel, ← pow_mul] using bounded

/-- The original finite supremum is bounded without enumerating the input domain. -/
lemma executionCoefficientBound_le_pow (width : Nat) :
    executionCoefficientBound width ≤ 2 ^ (width * (2 * width + 1)) := by
  unfold executionCoefficientBound
  apply Finset.sup_le
  intro input _member
  exact executionStates_magnitude_le ⟨input.1, input.2⟩

private lemma selectedBound_le_executionBound (width : Nat) :
    xgcdCoefficientBound width ≤ executionCoefficientBound width := by
  unfold xgcdCoefficientBound
  apply Finset.sup_le
  intro input _member
  let original : Input width := ⟨input.1, input.2⟩
  have finalBound := xgcdFinalState_coefficientMagnitude_le_bound original
  have left := (State.secondLeftCoefficient_natAbs_le_coefficientMagnitude
    (finalState original)).trans finalBound
  have right := (State.secondRightCoefficient_natAbs_le_coefficientMagnitude
    (finalState original)).trans finalBound
  change (finalState original).resultLeftCoefficient.natAbs ≤ _ at left
  change (finalState original).resultRightCoefficient.natAbs ≤ _ at right
  rw [xgcdFinalState_resultLeftCoefficient_eq_gcdA] at left
  rw [xgcdFinalState_resultRightCoefficient_eq_gcdB] at right
  exact max_le left right

/-- The actual execution width, including its original public-width maximum, is quadratic. -/
lemma executionCoefficientWidth_le_quadratic (width : Nat) :
    executionCoefficientWidth width ≤ width * (2 * width + 1) + 3 := by
  have executionSize : Nat.size (executionCoefficientBound width) ≤
      width * (2 * width + 1) + 1 := by
    simpa only [Nat.size_pow] using
      Nat.size_le_size (executionCoefficientBound_le_pow width)
  have selectedSize := Nat.size_le_size (selectedBound_le_executionBound width)
  unfold executionCoefficientWidth coefficientWidth
  exact max_le (by omega) (by omega)

/-- The original 257-bit-input XGCD execution workspace has this proved numeric ceiling. -/
lemma executionCoefficientWidth_257_le : executionCoefficientWidth 257 ≤ 132358 := by
  exact executionCoefficientWidth_le_quadratic 257

/-- The original 261-bit-input XGCD execution workspace has this proved numeric ceiling. -/
lemma executionCoefficientWidth_261_le : executionCoefficientWidth 261 ≤ 136506 := by
  exact executionCoefficientWidth_le_quadratic 261

end QuantumAlg.ClassicalAlgorithms.NumberTheory.XGCD
