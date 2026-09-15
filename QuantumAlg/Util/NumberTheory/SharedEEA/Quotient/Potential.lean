/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Iteration
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.IntervalCases

/-!
# Integer quotient-size potential for actual shared EEA steps

The source counts four phase steps per quotient bit and expresses two
successive Euclidean steps through their quotient matrices
[LYL+26, app_proof/sub_stepnum.tex:4-8,18-35]. This owner establishes
local integer inequalities for that exact recurrence, without the
source's sharp analytic constant or an assumed total step count.

Two positive quotients have enough squared recurrence growth to account
for both bit lengths. An unmatched final quotient is at least two and
satisfies the corresponding one-step inequality. In the other direction,
each actual active step decreases the remainder by a factor strictly less
than two to the quotient bit length, as used in the source lower-bound
argument [LYL+26, app_proof/sub_stepnum.tex:11-16]. Accumulation along an
actual terminating trajectory and its physical schedule remain separate.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.QuotientPotential

/-- The exact two-quotient recurrence factor pays for the sum of both quotient bit lengths. -/
theorem positive_pair_square (left right : Nat)
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    2 ^ (left.size + right.size) ≤ (left * right + 1) ^ 2 := by
  have leftSize := Nat.size_pos.mpr leftPositive
  have rightSize := Nat.size_pos.mpr rightPositive
  by_cases large : 4 ≤ left.size + right.size
  · have leftPower : 2 ^ (left.size - 1) ≤ left := Nat.lt_size.mp (by omega)
    have rightPower : 2 ^ (right.size - 1) ≤ right := Nat.lt_size.mp (by omega)
    have sumPred : (left.size - 1) + (right.size - 1) = left.size + right.size - 2 := by
      omega
    have productPower : 2 ^ (left.size + right.size - 2) ≤ left * right := by
      calc
        _ = 2 ^ (left.size - 1) * 2 ^ (right.size - 1) := by
          rw [← Nat.pow_add, sumPred]
        _ ≤ left * right := Nat.mul_le_mul leftPower rightPower
    calc
      _ ≤ 2 ^ ((left.size + right.size - 2) + (left.size + right.size - 2)) :=
        Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
      _ = (2 ^ (left.size + right.size - 2)) ^ 2 := by rw [Nat.pow_add, pow_two]
      _ ≤ (left * right) ^ 2 := Nat.pow_le_pow_left productPower 2
      _ ≤ (left * right + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  · have leftBound : left < 4 := (Nat.size_le (m := left) (n := 2)).mp (by omega)
    have rightBound : right < 4 := (Nat.size_le (m := right) (n := 2)).mp (by omega)
    interval_cases left <;> interval_cases right <;> decide

/-- A final quotient of at least two pays for its own bit length under the squared potential. -/
theorem final_quotient_square (quotient : Nat) (twoLe : 2 ≤ quotient) :
    2 ^ quotient.size ≤ quotient ^ 2 := by
  have lengthTwo : 2 ≤ quotient.size := by
    have oneLt : 1 < quotient.size := Nat.lt_size.mpr twoLe
    omega
  have lower : 2 ^ (quotient.size - 1) ≤ quotient := Nat.lt_size.mp (by omega)
  calc
    _ ≤ 2 ^ ((quotient.size - 1) + (quotient.size - 1)) :=
      Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    _ = (2 ^ (quotient.size - 1)) ^ 2 := by rw [Nat.pow_add, pow_two]
    _ ≤ quotient ^ 2 := Nat.pow_le_pow_left lower 2

/-- One actual macro step has the exact quotient-plus-remainder decomposition. -/
theorem decomposition (state : IterationState) :
    state.remainder = state.quotient * state.divisor + (IterationState.step state).divisor := by
  change state.remainder = (state.remainder / state.divisor) * state.divisor +
    state.remainder % state.divisor
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod state.remainder state.divisor).symm

/-- Two actual macro steps have the exact continuant factor, including the residual term. -/
theorem two_step_decomposition (state : IterationState) :
    state.remainder =
      (state.quotient * (IterationState.step state).quotient + 1) *
          (IterationState.step (IterationState.step state)).remainder +
        state.quotient * (IterationState.step (IterationState.step state)).divisor := by
  calc
    _ = state.quotient * state.divisor + (IterationState.step state).divisor := decomposition state
    _ = state.quotient * ((IterationState.step state).quotient *
          (IterationState.step state).divisor +
            (IterationState.step (IterationState.step state)).divisor) +
        (IterationState.step state).divisor :=
      congrArg (fun value => state.quotient * value + (IterationState.step state).divisor)
        (decomposition (IterationState.step state))
    _ = _ := by
      change _ = (state.quotient * (IterationState.step state).quotient + 1) *
          (IterationState.step state).divisor +
        state.quotient * (IterationState.step (IterationState.step state)).divisor
      ring

/-- Every genuine active quotient step has the strict factor bound used by the lower potential. -/
theorem step_strict (state : IterationState) (active : 0 < state.divisor) :
    state.remainder < 2 ^ state.quotient.size * (IterationState.step state).remainder := by
  have remainderBound : (IterationState.step state).divisor < state.divisor :=
    Nat.mod_lt _ active
  have digitBound : state.quotient + 1 ≤ 2 ^ state.quotient.size := by
    have := Nat.lt_size_self state.quotient
    omega
  calc
    _ = state.quotient * state.divisor + (IterationState.step state).divisor := decomposition state
    _ < state.quotient * state.divisor + state.divisor :=
      Nat.add_lt_add_left remainderBound _
    _ = (state.quotient + 1) * state.divisor := by ring
    _ ≤ 2 ^ state.quotient.size * state.divisor := Nat.mul_le_mul_right _ digitBound

/-- Every actual active pair decreases the squared remainder by both quotient-size factors. -/
theorem two_step_square (state : IterationState) (ordered : state.divisor < state.remainder)
    (active : 0 < state.divisor) (nextActive : 0 < (IterationState.step state).divisor) :
    2 ^ (state.quotient.size + (IterationState.step state).quotient.size) *
        (IterationState.step (IterationState.step state)).remainder ^ 2 ≤ state.remainder ^ 2 := by
  have firstPositive := IterationState.quotient_pos state ordered active
  have nextOrdered : (IterationState.step state).divisor < (IterationState.step state).remainder :=
    IterationState.step_divisor_lt state active
  have secondPositive := IterationState.quotient_pos (IterationState.step state)
    nextOrdered nextActive
  have quotientBound := positive_pair_square state.quotient (IterationState.step state).quotient
    firstPositive secondPositive
  have factorBound : (state.quotient * (IterationState.step state).quotient + 1) *
      (IterationState.step (IterationState.step state)).remainder ≤ state.remainder := by
    have exactRecurrence := two_step_decomposition state
    omega
  calc
    _ ≤ (state.quotient * (IterationState.step state).quotient + 1) ^ 2 *
        (IterationState.step (IterationState.step state)).remainder ^ 2 :=
      Nat.mul_le_mul_right _ quotientBound
    _ = ((state.quotient * (IterationState.step state).quotient + 1) *
        (IterationState.step (IterationState.step state)).remainder) ^ 2 := by ring
    _ ≤ state.remainder ^ 2 := Nat.pow_le_pow_left factorBound 2

/-- A genuine final division has quotient at least two, including the smallest prime input. -/
theorem terminal_quotient_two (state : IterationState)
    (ordered : state.divisor < state.remainder) (active : 0 < state.divisor)
    (finished : (IterationState.step state).divisor = 0) : 2 ≤ state.quotient := by
  have positive := IterationState.quotient_pos state ordered active
  have exactDivision := decomposition state
  rw [finished, Nat.add_zero] at exactDivision
  by_contra small
  have one : state.quotient = 1 := by omega
  rw [one, Nat.one_mul] at exactDivision
  omega

/-- A genuine final step pays for the unmatched quotient without adding a boundary assumption. -/
theorem terminal_step_square (state : IterationState)
    (ordered : state.divisor < state.remainder) (active : 0 < state.divisor)
    (finished : (IterationState.step state).divisor = 0) :
    2 ^ state.quotient.size * (IterationState.step state).remainder ^ 2 ≤ state.remainder ^ 2 := by
  have quotientBound := final_quotient_square state.quotient
    (terminal_quotient_two state ordered active finished)
  have exactDivision := decomposition state
  rw [finished, Nat.add_zero] at exactDivision
  calc
    _ ≤ state.quotient ^ 2 * state.divisor ^ 2 := Nat.mul_le_mul_right _ quotientBound
    _ = (state.quotient * state.divisor) ^ 2 := by ring
    _ = state.remainder ^ 2 := congrArg (fun value => value ^ 2) exactDivision.symm

end QuantumAlg.NumberTheory.SharedEEA.QuotientPotential
