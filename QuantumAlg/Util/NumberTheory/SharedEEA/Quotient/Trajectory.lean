/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Potential

/-!
# Integer potentials along the actual active macro trajectory

The source's active four-phase step count is four times the sum of the
actual quotient bit lengths [LYL+26, app_proof/sub_stepnum.tex:4-16].
This owner accumulates the proved integer factors along precisely the
active `IterationState.step` recurrence. Its stopping function describes
only that mathematical active trajectory; it is not a proposed physical
idle operation or a definition of terminal circuit padding.

The squared potential groups actual steps in pairs and handles an odd
final step with its proved terminal quotient bound. The ordinary strict
potential supplies the lower bound when the terminal gcd is one. A
separate termination proof must supply sufficient fuel before these
complete-trajectory bounds can become an independent fixed schedule.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.QuotientTrajectory

/-- Follow only actual active macro steps, stopping this mathematical trace at divisor zero. -/
def activeRun : Nat → IterationState → IterationState
  | 0, state => state
  | fuel + 1, state =>
      if state.divisor = 0 then state else activeRun fuel (IterationState.step state)

/-- Sum only the bit lengths of quotients belonging to actual active macro steps. -/
def weight : Nat → IterationState → Nat
  | 0, _state => 0
  | fuel + 1, state =>
      if state.divisor = 0 then 0 else state.quotient.size + weight fuel (IterationState.step state)

/-- A terminal mathematical trace has no additional macro states. -/
theorem activeRun_finished (fuel : Nat) (state : IterationState) (finished : state.divisor = 0) :
    activeRun fuel state = state := by
  cases fuel <;> simp only [activeRun, if_pos finished]

/-- A terminal mathematical trace contains no extra quotient contribution. -/
theorem weight_finished (fuel : Nat) (state : IterationState) (finished : state.divisor = 0) :
    weight fuel state = 0 := by
  cases fuel <;> simp only [weight, if_pos finished]

/-- Every actual macro state retains strictly ordered remainders, including its terminal state. -/
theorem activeRun_ordered (fuel : Nat) (state : IterationState)
    (ordered : state.divisor < state.remainder) :
    (activeRun fuel state).divisor < (activeRun fuel state).remainder := by
  induction fuel generalizing state with
  | zero => exact ordered
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simpa only [activeRun, if_pos finished] using ordered
    · rw [activeRun, if_neg finished]
      exact inductionHypothesis (IterationState.step state)
        (IterationState.step_divisor_lt state (Nat.pos_of_ne_zero finished))

/-- The actual active trajectory preserves the original remainder gcd. -/
theorem activeRun_gcd (fuel : Nat) (state : IterationState) :
    Nat.gcd (activeRun fuel state).remainder (activeRun fuel state).divisor =
      Nat.gcd state.remainder state.divisor := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
    by_cases finished : state.divisor = 0
    · simp only [activeRun, if_pos finished]
    · rw [activeRun, if_neg finished]
      exact (inductionHypothesis (IterationState.step state)).trans (IterationState.step_gcd state)

/-- The squared local factors telescope along every fully completed active trajectory. -/
theorem square_bound : ∀ (fuel : Nat) (state : IterationState),
    state.divisor < state.remainder → (activeRun fuel state).divisor = 0 →
      2 ^ weight fuel state * (activeRun fuel state).remainder ^ 2 ≤ state.remainder ^ 2 := by
  apply Nat.twoStepInduction
  · intro state _ordered _finished
    simp only [weight, activeRun, Nat.pow_zero, Nat.one_mul, le_refl]
  · intro state ordered finished
    by_cases done : state.divisor = 0
    · simp only [weight, activeRun, if_pos done, Nat.pow_zero, Nat.one_mul, le_refl]
    · have nextDone : (IterationState.step state).divisor = 0 := by
        simpa only [activeRun, if_neg done] using finished
      simpa only [weight, activeRun, if_neg done, Nat.add_zero] using
        QuotientPotential.terminal_step_square state ordered (Nat.pos_of_ne_zero done) nextDone
  · intro fuel inductionHypothesis _ state ordered finished
    by_cases done : state.divisor = 0
    · simp only [weight, activeRun, if_pos done, Nat.pow_zero, Nat.one_mul, le_refl]
    · have active := Nat.pos_of_ne_zero done
      by_cases nextDone : (IterationState.step state).divisor = 0
      · rw [weight, if_neg done, weight_finished _ _ nextDone, Nat.add_zero,
          activeRun, if_neg done, activeRun_finished _ _ nextDone]
        exact QuotientPotential.terminal_step_square state ordered active nextDone
      · have nextActive := Nat.pos_of_ne_zero nextDone
        have twiceOrdered : (IterationState.step (IterationState.step state)).divisor <
            (IterationState.step (IterationState.step state)).remainder :=
          IterationState.step_divisor_lt (IterationState.step state) nextActive
        have twiceFinished :
            (activeRun fuel (IterationState.step (IterationState.step state))).divisor = 0 := by
          simpa only [activeRun, if_neg done, if_neg nextDone] using finished
        have remainingBound := inductionHypothesis
          (IterationState.step (IterationState.step state)) twiceOrdered twiceFinished
        calc
          _ = 2 ^ (state.quotient.size + (IterationState.step state).quotient.size) *
              (2 ^ weight fuel (IterationState.step (IterationState.step state)) *
                (activeRun fuel
                  (IterationState.step (IterationState.step state))).remainder ^ 2) := by
            simp only [weight, activeRun, if_neg done, if_neg nextDone, Nat.pow_add]
            ring
          _ ≤ 2 ^ (state.quotient.size + (IterationState.step state).quotient.size) *
              (IterationState.step (IterationState.step state)).remainder ^ 2 :=
            Nat.mul_le_mul_left _ remainingBound
          _ ≤ state.remainder ^ 2 :=
            QuotientPotential.two_step_square state ordered active nextActive

/-- The ordinary local factors telescope even along an unfinished active prefix. -/
theorem linear_bound (fuel : Nat) (state : IterationState) :
    state.remainder ≤ 2 ^ weight fuel state * (activeRun fuel state).remainder := by
  induction fuel generalizing state with
  | zero => simp only [weight, activeRun, Nat.pow_zero, Nat.one_mul, le_refl]
  | succ fuel inductionHypothesis =>
    by_cases done : state.divisor = 0
    · simp only [weight, activeRun, if_pos done, Nat.pow_zero, Nat.one_mul, le_refl]
    · rw [weight, if_neg done, activeRun, if_neg done]
      calc
        _ ≤ 2 ^ state.quotient.size * (IterationState.step state).remainder :=
          (QuotientPotential.step_strict state (Nat.pos_of_ne_zero done)).le
        _ ≤ 2 ^ state.quotient.size *
            (2 ^ weight fuel (IterationState.step state) *
              (activeRun fuel (IterationState.step state)).remainder) :=
          Nat.mul_le_mul_left _ (inductionHypothesis (IterationState.step state))
        _ = _ := by rw [Nat.pow_add]; ring

/-- A nonempty active prefix retains the strict factor needed for the source lower bound. -/
theorem linear_strict (fuel : Nat) (state : IterationState) (active : 0 < state.divisor) :
    state.remainder < 2 ^ weight (fuel + 1) state * (activeRun (fuel + 1) state).remainder := by
  rw [weight, if_neg (Nat.ne_of_gt active), activeRun, if_neg (Nat.ne_of_gt active)]
  calc
    _ < 2 ^ state.quotient.size * (IterationState.step state).remainder :=
      QuotientPotential.step_strict state active
    _ ≤ 2 ^ state.quotient.size *
        (2 ^ weight fuel (IterationState.step state) *
          (activeRun fuel (IterationState.step state)).remainder) :=
      Nat.mul_le_mul_left _ (linear_bound fuel (IterationState.step state))
    _ = _ := by rw [Nat.pow_add]; ring

/-- The complete actual quotient weight is strictly below twice the leading remainder bit length. -/
theorem weight_lt_twice_size (fuel : Nat) (state : IterationState)
    (ordered : state.divisor < state.remainder) (finished : (activeRun fuel state).divisor = 0) :
    weight fuel state < 2 * state.remainder.size := by
  have terminalOrdered := activeRun_ordered fuel state ordered
  have positive : 0 < (activeRun fuel state).remainder := by omega
  have oneLe := Nat.one_le_pow 2 (activeRun fuel state).remainder positive
  have weightPower : 2 ^ weight fuel state ≤ state.remainder ^ 2 := by
    calc
      _ = 2 ^ weight fuel state * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ weight fuel state * (activeRun fuel state).remainder ^ 2 :=
        Nat.mul_le_mul_left _ oneLe
      _ ≤ state.remainder ^ 2 := square_bound fuel state ordered finished
  have upper : state.remainder ^ 2 < 2 ^ (2 * state.remainder.size) := by
    calc
      _ < (2 ^ state.remainder.size) ^ 2 :=
        Nat.pow_lt_pow_left (Nat.lt_size_self state.remainder) (by decide : 2 ≠ 0)
      _ = 2 ^ (2 * state.remainder.size) := by rw [pow_two, ← Nat.pow_add, Nat.two_mul]
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (weightPower.trans_lt upper)

/-- A completed gcd-one trajectory has at least the original leading remainder's bit length. -/
theorem size_le_weight (fuel : Nat) (state : IterationState) (active : 0 < state.divisor)
    (finished : (activeRun fuel state).divisor = 0)
    (coprime : Nat.gcd state.remainder state.divisor = 1) :
    state.remainder.size ≤ weight fuel state := by
  have gcdPreserved := activeRun_gcd fuel state
  have terminalOne : (activeRun fuel state).remainder = 1 := by
    simpa only [finished, Nat.gcd_zero_right, coprime] using gcdPreserved
  cases fuel with
  | zero =>
    change state.divisor = 0 at finished
    omega
  | succ fuel =>
    have strict := linear_strict fuel state active
    rw [terminalOne, Nat.mul_one] at strict
    exact Nat.size_le.mpr strict

end QuantumAlg.NumberTheory.SharedEEA.QuotientTrajectory
