/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Iteration
import Mathlib.Data.Nat.Size

/-!
# Shared-EEA bit capacity from the conserved cross-sum

The source obtains shared storage from `r*t + r'*t' = p`
[LYL+26, sec_EEA/sub_regshare.tex:4-12]. These exact natural-number bounds
include zero coordinates at initialization and termination. For positive
factors, the sum of their bit lengths exceeds the modulus bit length by
at most one for a pair, and by at most two for a triple.

The iteration-boundary corollaries justify both pair payloads and the
additional coefficient zero bit [LYL+26, sec_EEA/sub_regshare.tex:16-20].
They do not yet establish every intermediate triple or rotated-word
capacity; those require the actual phase invariants in addition to the
macro cross-sum. No register is encoded merely by a dimension equality.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.Capacity

/-- Positive factors whose product is bounded share at most one extra binary digit. -/
theorem positive_pair_size (left right modulus : Nat)
    (leftPositive : 0 < left) (rightPositive : 0 < right)
    (productBound : left * right ≤ modulus) :
    left.size + right.size ≤ modulus.size + 1 := by
  have leftSize : 0 < left.size := Nat.size_pos.mpr leftPositive
  have rightSize : 0 < right.size := Nat.size_pos.mpr rightPositive
  have leftPower : 2 ^ (left.size - 1) ≤ left := Nat.lt_size.mp (by omega)
  have rightPower : 2 ^ (right.size - 1) ≤ right := Nat.lt_size.mp (by omega)
  have productPower : 2 ^ ((left.size - 1) + (right.size - 1)) ≤ left * right := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul leftPower rightPower
  have powerBound := productPower.trans_lt (productBound.trans_lt (Nat.lt_size_self modulus))
  have lengthBound := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp powerBound
  omega

/-- Individual bounds cover the source's zero-factor boundary cases as well. -/
theorem pair_size (left right modulus : Nat)
    (leftBound : left ≤ modulus) (rightBound : right ≤ modulus)
    (productBound : left * right ≤ modulus) :
    left.size + right.size ≤ modulus.size + 1 := by
  by_cases leftZero : left = 0
  · have rightSize := Nat.size_le_size rightBound
    simp only [leftZero, Nat.size_zero, Nat.zero_add]
    omega
  · by_cases rightZero : right = 0
    · have leftSize := Nat.size_le_size leftBound
      simp only [rightZero, Nat.size_zero, Nat.add_zero]
      omega
    · exact positive_pair_size left right modulus (Nat.pos_of_ne_zero leftZero)
        (Nat.pos_of_ne_zero rightZero) productBound

/-- A positive triple costs at most two extra digits beyond its bounded product. -/
theorem positive_triple_size (first second third modulus : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) (thirdPositive : 0 < third)
    (productBound : first * second * third ≤ modulus) :
    first.size + second.size + third.size ≤ modulus.size + 2 := by
  have firstPair := positive_pair_size first second (first * second)
    firstPositive secondPositive le_rfl
  have secondPair := positive_pair_size (first * second) third modulus
    (Nat.mul_pos firstPositive secondPositive) thirdPositive productBound
  omega

/-- Replacing zero coordinates by one gives a uniform sufficient triple-capacity condition. -/
theorem triple_size_of_clamped_product (first second third modulus : Nat)
    (productBound : max first 1 * max second 1 * max third 1 ≤ modulus) :
    first.size + second.size + third.size ≤ modulus.size + 2 := by
  have firstPositive : 0 < max first 1 := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have secondPositive : 0 < max second 1 := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have thirdPositive : 0 < max third 1 := lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _)
  have capacity := positive_triple_size (max first 1) (max second 1) (max third 1) modulus
    firstPositive secondPositive thirdPositive productBound
  have firstSize := Nat.size_le_size (le_max_left first 1)
  have secondSize := Nat.size_le_size (le_max_left second 1)
  have thirdSize := Nat.size_le_size (le_max_left third 1)
  omega

/-- Every reachable macro coordinate is bounded by the conserved source modulus. -/
theorem iteration_fields_le (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.remainder ≤ modulus ∧ state.divisor ≤ modulus ∧
      state.coefficient ≤ modulus ∧ state.previousCoefficient ≤ modulus := by
  have productBound := (IterationState.products_le_balance state).1
  rw [conserved] at productBound
  have remainderPositive : 0 < state.remainder :=
    (Nat.zero_le state.divisor).trans_lt valid.divisor_lt
  have remainderBound :=
    (Nat.le_mul_of_pos_right state.remainder valid.coefficient_pos).trans productBound
  have coefficientBound :=
    (Nat.le_mul_of_pos_left state.coefficient remainderPositive).trans productBound
  exact ⟨remainderBound, (Nat.le_of_lt valid.divisor_lt).trans remainderBound,
    coefficientBound, (Nat.le_of_lt valid.previous_lt).trans coefficientBound⟩

/-- Both exact source pair payloads fit within the modulus bit length plus one. -/
theorem iteration_pair_sizes (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.remainder.size + state.coefficient.size ≤ modulus.size + 1 ∧
      state.divisor.size + state.previousCoefficient.size ≤ modulus.size + 1 := by
  obtain ⟨remainderBound, divisorBound, coefficientBound, previousBound⟩ :=
    iteration_fields_le state modulus valid conserved
  have products := IterationState.products_le_balance state
  rw [conserved] at products
  exact ⟨pair_size _ _ _ remainderBound coefficientBound products.1,
    pair_size _ _ _ divisorBound previousBound products.2⟩

/-- At macro boundaries the prescribed coefficient zero bit fits in the actual source words. -/
theorem iteration_word_capacity (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.coefficient.size + 1 + state.remainder.size ≤ modulus.size + 3 ∧
      state.previousCoefficient.size + state.divisor.size ≤ modulus.size + 3 := by
  have capacities := iteration_pair_sizes state modulus valid conserved
  omega

/-- Every original positive input establishes the shared pair capacities after its actual fold. -/
theorem folded_pair_sizes (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    let state := IterationState.initial modulus (foldInput modulus input).2
    state.remainder.size + state.coefficient.size ≤ modulus.size + 1 ∧
      state.divisor.size + state.previousCoefficient.size ≤ modulus.size + 1 :=
  iteration_pair_sizes _ modulus (folded_initial_admissible modulus input positive bounded)
    (IterationState.initial_balance modulus _)

/-- The terminal zero divisor remains covered after a genuine active macro iteration. -/
theorem step_pair_sizes (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) (active : 0 < state.divisor) :
    (IterationState.step state).remainder.size + (IterationState.step state).coefficient.size ≤
        modulus.size + 1 ∧
      (IterationState.step state).divisor.size +
          (IterationState.step state).previousCoefficient.size ≤ modulus.size + 1 :=
  iteration_pair_sizes (IterationState.step state) modulus
    (IterationState.step_admissible state valid active)
    ((IterationState.step_balance state).trans conserved)

end QuantumAlg.NumberTheory.SharedEEA.Capacity
