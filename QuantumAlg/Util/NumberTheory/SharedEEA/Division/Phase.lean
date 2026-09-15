/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Phase
import Mathlib.Tactic.Ring

/-!
# Exact quotient-extraction microsteps of the shared EEA

Phase two first shifts the aligned divisor right, then conditionally
subtracts it and writes the resulting quotient bit
[LYL+26, sec_EEA/sub_4phase.tex:8-22]. The effective most-significant
quotient prefix is stored as described in `sec_EEA/sub_regshare.tex:16-17`;
its source numerical value is `quotientPrefix * scale`. The written-bit count is
the source length coordinate `ℓ_q`, incremented with each microstep
[LYL+26, sec_EEA/sub_regshare.tex:279-287].

The written digit recovers the conditional subtraction, so the reverse
step reconstructs the old remainder, prefix, scale, and written-bit count.
Both equality at the subtraction threshold and zero remainders are included.
The complete arithmetic phase computes the ordinary quotient and remainder,
and its actual quotient initializes the already proved coefficient phase.

This module consumes an aligned scale and its actual shift count from the
first phase. The internal entry conditions say that the scale is the
corresponding power of two and that its shifted divisor strictly exceeds
the dividend. Neither initialization nor execution computes the quotient
in advance. A first-phase construction must establish these conditions
from the original input; they are not additional caller-domain assumptions.
Physical packing, sign/phase flag refinement, and retained `Γ` recovery are
not claimed by these decoded arithmetic laws.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionPhase

/-- Decoded remainder, effective quotient prefix, and the source's two length coordinates. -/
@[ext]
structure State where
  /-- The dividend after contributions from already written quotient bits. -/
  remainder : Nat
  /-- Effective quotient bits written so far, in their numerical prefix order. -/
  quotientPrefix : Nat
  /-- The binary place before the next right shift. -/
  scale : Nat
  /-- Actual quotient-bit length, incremented by every source phase-two step. -/
  written : Nat
deriving DecidableEq

/-- Shift right, conditionally subtract, and append the actual comparison result as a bit. -/
def step (divisor : Nat) (state : State) : State :=
  let place := state.scale / 2
  let subtract := place * divisor ≤ state.remainder
  ⟨if subtract then state.remainder - place * divisor else state.remainder,
    2 * state.quotientPrefix + if subtract then 1 else 0, place, state.written + 1⟩

/-- Read back the written bit and reconstruct every preceding arithmetic/length coordinate. -/
def rewind (divisor : Nat) (state : State) : State :=
  ⟨state.remainder + (state.quotientPrefix % 2) * (state.scale * divisor),
    state.quotientPrefix / 2, 2 * state.scale, state.written - 1⟩

/-- The lowest written quotient digit is exactly the source's weak subtraction comparison. -/
theorem step_digit (divisor : Nat) (state : State) :
    (step divisor state).quotientPrefix % 2 =
      if state.scale / 2 * divisor ≤ state.remainder then 1 else 0 := by
  change (2 * state.quotientPrefix +
    (if state.scale / 2 * divisor ≤ state.remainder then 1 else 0)) % 2 = _
  by_cases subtract : state.scale / 2 * divisor ≤ state.remainder
  · simp only [if_pos subtract]
    omega
  · simp only [if_neg subtract]
    omega

/-- The coefficient phase will read precisely the actual bit written by this subtraction. -/
theorem step_lowBit (divisor : Nat) (state : State) :
    CoefficientPhase.lowBit (step divisor state).quotientPrefix =
      decide (state.scale / 2 * divisor ≤ state.remainder) := by
  unfold CoefficientPhase.lowBit
  rw [step_digit]
  by_cases subtract : state.scale / 2 * divisor ≤ state.remainder <;> simp [subtract]

/-- Removing the written bit recovers the exact old quotient prefix. -/
theorem step_prefix_div (divisor : Nat) (state : State) :
    (step divisor state).quotientPrefix / 2 = state.quotientPrefix := by
  change (2 * state.quotientPrefix +
    (if state.scale / 2 * divisor ≤ state.remainder then 1 else 0)) / 2 = _
  by_cases subtract : state.scale / 2 * divisor ≤ state.remainder
  · simp only [if_pos subtract]
    omega
  · simp only [if_neg subtract]
    omega

/-- The actual phase-two step has a left inverse whenever its scale admits the right shift. -/
theorem rewind_step (divisor : Nat) (state : State)
    (evenScale : 2 * (state.scale / 2) = state.scale) :
    rewind divisor (step divisor state) = state := by
  apply State.ext
  · change (step divisor state).remainder +
      ((step divisor state).quotientPrefix % 2) * ((step divisor state).scale * divisor) =
        state.remainder
    rw [step_digit]
    change (if state.scale / 2 * divisor ≤ state.remainder then
        state.remainder - state.scale / 2 * divisor else state.remainder) +
      (if state.scale / 2 * divisor ≤ state.remainder then 1 else 0) *
        (state.scale / 2 * divisor) = state.remainder
    by_cases subtract : state.scale / 2 * divisor ≤ state.remainder
    · simpa only [if_pos subtract, one_mul] using Nat.sub_add_cancel subtract
    · simp only [if_neg subtract, zero_mul, Nat.add_zero]
  · exact step_prefix_div divisor state
  · exact evenScale
  · change (state.written + 1) - 1 = state.written
    omega

/-- No valid source microstates are merged by quotient-bit extraction. -/
theorem step_injective {divisor : Nat} {left right : State}
    (leftEven : 2 * (left.scale / 2) = left.scale)
    (rightEven : 2 * (right.scale / 2) = right.scale)
    (same : step divisor left = step divisor right) : left = right := by
  calc
    left = rewind divisor (step divisor left) := (rewind_step divisor left leftEven).symm
    _ = rewind divisor (step divisor right) := congrArg (rewind divisor) same
    _ = right := rewind_step divisor right rightEven

/-- The original dividend expressed by the current remainder and written weighted quotient. -/
def total (divisor : Nat) (state : State) : Nat :=
  state.remainder + state.quotientPrefix * state.scale * divisor

/-- Conditional subtraction and actual quotient-bit writing conserve the exact dividend. -/
theorem step_total (divisor : Nat) (state : State)
    (evenScale : 2 * (state.scale / 2) = state.scale) :
    total divisor (step divisor state) = total divisor state := by
  by_cases subtract : state.scale / 2 * divisor ≤ state.remainder
  · change (if state.scale / 2 * divisor ≤ state.remainder then
        state.remainder - state.scale / 2 * divisor else state.remainder) +
      (2 * state.quotientPrefix + if state.scale / 2 * divisor ≤ state.remainder then 1 else 0) *
        (state.scale / 2) * divisor = _
    simp only [if_pos subtract]
    calc
      _ = (state.remainder - state.scale / 2 * divisor + state.scale / 2 * divisor) +
          state.quotientPrefix * (2 * (state.scale / 2)) * divisor := by ring
      _ = total divisor state := by rw [Nat.sub_add_cancel subtract, evenScale]; rfl
  · change (if state.scale / 2 * divisor ≤ state.remainder then
        state.remainder - state.scale / 2 * divisor else state.remainder) +
      (2 * state.quotientPrefix + if state.scale / 2 * divisor ≤ state.remainder then 1 else 0) *
        (state.scale / 2) * divisor = _
    simp only [if_neg subtract]
    calc
      _ = state.remainder + state.quotientPrefix * (2 * (state.scale / 2)) * divisor := by ring
      _ = total divisor state := by rw [evenScale]; rfl

/-- A source phase-two remainder fits strictly below the current aligned divisor. -/
def Below (divisor : Nat) (state : State) : Prop :=
  state.remainder < state.scale * divisor

/-- The weak comparison produces the strict remainder bound at the next binary place. -/
theorem step_below (divisor : Nat) (state : State)
    (evenScale : 2 * (state.scale / 2) = state.scale) (below : Below divisor state) :
    Below divisor (step divisor state) := by
  have previousBound : state.remainder < 2 * (state.scale / 2 * divisor) := by
    calc
      state.remainder < state.scale * divisor := below
      _ = (2 * (state.scale / 2)) * divisor :=
        congrArg (fun scale : Nat => scale * divisor) evenScale.symm
      _ = _ := by ring
  change (if state.scale / 2 * divisor ≤ state.remainder then
    state.remainder - state.scale / 2 * divisor else state.remainder) <
      state.scale / 2 * divisor
  by_cases subtract : state.scale / 2 * divisor ≤ state.remainder
  · simp only [if_pos subtract]
    omega
  · simp only [if_neg subtract]
    omega

private theorem power_scale_shift (divisor places : Nat) (state : State)
    (scale : state.scale = 2 ^ (places + 1)) :
    (step divisor state).scale = 2 ^ places := by
  change state.scale / 2 = 2 ^ places
  rw [scale, Nat.pow_succ]
  exact Nat.mul_div_left _ (by decide : 0 < 2)

private theorem power_scale_even (places : Nat) (state : State)
    (scale : state.scale = 2 ^ (places + 1)) :
    2 * (state.scale / 2) = state.scale := by
  rw [scale, Nat.pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
  omega

/-- Perform the indicated number of actual quotient-extraction microsteps. -/
def run (divisor : Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => run divisor count (step divisor state)

/-- Reverse the same number of steps, including their retained written-bit coordinate. -/
def rewindRun (divisor : Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => rewind divisor (rewindRun divisor count state)

/-- The complete phase's final scale is one, after exactly its actual alignment count. -/
theorem run_scale (divisor places : Nat) (state : State) (scale : state.scale = 2 ^ places) :
    (run divisor places state).scale = 1 := by
  induction places generalizing state with
  | zero => simpa only [run, Nat.pow_zero] using scale
  | succ places inductionHypothesis =>
    exact inductionHypothesis (step divisor state) (power_scale_shift divisor places state scale)

/-- The actual quotient-length coordinate records every performed microstep. -/
theorem run_written (divisor places : Nat) (state : State) :
    (run divisor places state).written = state.written + places := by
  induction places generalizing state with
  | zero => simp [run]
  | succ places inductionHypothesis =>
    change (run divisor places (step divisor state)).written = state.written + (places + 1)
    rw [inductionHypothesis]
    change (state.written + 1) + places = state.written + (places + 1)
    omega

/-- All actual division steps preserve the original dividend. -/
theorem run_total (divisor places : Nat) (state : State) (scale : state.scale = 2 ^ places) :
    total divisor (run divisor places state) = total divisor state := by
  induction places generalizing state with
  | zero => rfl
  | succ places inductionHypothesis =>
    exact (inductionHypothesis (step divisor state)
      (power_scale_shift divisor places state scale)).trans
        (step_total divisor state (power_scale_even places state scale))

/-- The phase's final remainder satisfies the ordinary Euclidean remainder range. -/
theorem run_below (divisor places : Nat) (state : State)
    (scale : state.scale = 2 ^ places) (below : Below divisor state) :
    Below divisor (run divisor places state) := by
  induction places generalizing state with
  | zero => exact below
  | succ places inductionHypothesis =>
    exact inductionHypothesis (step divisor state) (power_scale_shift divisor places state scale)
      (step_below divisor state (power_scale_even places state scale) below)

/-- The entire actual phase has a left inverse, without discarding its quotient or lengths. -/
theorem rewindRun_run (divisor places : Nat) (state : State)
    (scale : state.scale = 2 ^ places) :
    rewindRun divisor places (run divisor places state) = state := by
  induction places generalizing state with
  | zero => rfl
  | succ places inductionHypothesis =>
    change rewind divisor
      (rewindRun divisor places (run divisor places (step divisor state))) = state
    rw [inductionHypothesis (step divisor state) (power_scale_shift divisor places state scale)]
    exact rewind_step divisor state (power_scale_even places state scale)

/-- Enter phase two with its actual aligned scale and an empty quotient word. -/
def start (dividend scale : Nat) : State := ⟨dividend, 0, scale, 0⟩

/-- Consume the actual alignment count; initialization never computes a quotient. -/
def divide (divisor dividend scale places : Nat) : State :=
  run divisor places (start dividend scale)

/-- Final division data satisfy the exact dividend decomposition and remainder bound. -/
theorem divide_spec (divisor dividend scale places : Nat)
    (aligned : scale = 2 ^ places) (upper : dividend < scale * divisor) :
    (divide divisor dividend scale places).remainder +
        (divide divisor dividend scale places).quotientPrefix * divisor = dividend ∧
      (divide divisor dividend scale places).remainder < divisor := by
  have finalScale := run_scale divisor places (start dividend scale) aligned
  have conserved := run_total divisor places (start dividend scale) aligned
  have finalBound := run_below divisor places (start dividend scale) aligned upper
  change (divide divisor dividend scale places).scale = 1 at finalScale
  change (divide divisor dividend scale places).remainder +
      (divide divisor dividend scale places).quotientPrefix *
        (divide divisor dividend scale places).scale * divisor = dividend + 0 * scale * divisor
      at conserved
  change (divide divisor dividend scale places).remainder <
    (divide divisor dividend scale places).scale * divisor at finalBound
  simpa only [finalScale, Nat.mul_one, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using
    And.intro conserved finalBound

/-- The actual written prefix is exactly the Euclidean quotient. -/
theorem divide_quotient (divisor dividend scale places : Nat)
    (aligned : scale = 2 ^ places) (upper : dividend < scale * divisor) :
    (divide divisor dividend scale places).quotientPrefix = dividend / divisor := by
  obtain ⟨decomposition, remainderBound⟩ := divide_spec divisor dividend scale places aligned upper
  symm
  apply Nat.div_eq_of_lt_le
  · omega
  · calc
      dividend = (divide divisor dividend scale places).remainder +
          (divide divisor dividend scale places).quotientPrefix * divisor := decomposition.symm
      _ < divisor + (divide divisor dividend scale places).quotientPrefix * divisor :=
        Nat.add_lt_add_right remainderBound _
      _ = ((divide divisor dividend scale places).quotientPrefix + 1) * divisor := by ring

/-- The conditionally subtracted result is exactly the Euclidean remainder. -/
theorem divide_remainder (divisor dividend scale places : Nat)
    (aligned : scale = 2 ^ places) (upper : dividend < scale * divisor) :
    (divide divisor dividend scale places).remainder = dividend % divisor := by
  obtain ⟨decomposition, remainderBound⟩ := divide_spec divisor dividend scale places aligned upper
  calc
    _ = ((divide divisor dividend scale places).remainder +
        (divide divisor dividend scale places).quotientPrefix * divisor) % divisor := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt remainderBound]
    _ = dividend % divisor := congrArg (fun value : Nat => value % divisor) decomposition

/-- The source's written-bit length retains the exact count needed to reverse the whole phase. -/
theorem divide_reversible (divisor dividend scale places : Nat) (aligned : scale = 2 ^ places) :
    rewindRun divisor (divide divisor dividend scale places).written
        (divide divisor dividend scale places) = start dividend scale := by
  have written := run_written divisor places (start dividend scale)
  change (divide divisor dividend scale places).written = 0 + places at written
  rw [written, Nat.zero_add]
  exact rewindRun_run divisor places (start dividend scale) aligned

/-- Pass the actually written quotient to the coefficient phase, retaining the EEA coefficients. -/
def coefficientStart (state : IterationState) (division : State) : CoefficientPhase.State :=
  ⟨state.previousCoefficient, division.quotientPrefix, 1⟩

/-- The actual division output initializes exactly the coefficient phase of the same macro step. -/
theorem coefficientStart_divide (state : IterationState) (scale places : Nat)
    (aligned : scale = 2 ^ places) (upper : state.remainder < scale * state.divisor) :
    coefficientStart state (divide state.divisor state.remainder scale places) =
      CoefficientPhase.start state := by
  apply CoefficientPhase.State.ext
  · rfl
  · exact divide_quotient state.divisor state.remainder scale places aligned upper
  · rfl

/-- Both complete actual arithmetic phases produce the two updated macro-step coordinates. -/
theorem division_coefficient_coordinates (state : IterationState) (scale places : Nat)
    (aligned : scale = 2 ^ places) (upper : state.remainder < scale * state.divisor) :
    let division := divide state.divisor state.remainder scale places
    division.remainder = (IterationState.step state).divisor ∧
      (CoefficientPhase.finish state.coefficient (coefficientStart state division)).value =
        (IterationState.step state).coefficient := by
  constructor
  · exact divide_remainder state.divisor state.remainder scale places aligned upper
  · rw [coefficientStart_divide state scale places aligned upper]
    exact CoefficientPhase.finish_start_coefficient state

/-- The smallest valid input writes the equality-boundary high bit, then the final zero bit. -/
theorem smallest_input_two_microsteps :
    step 1 (start 2 4) = ⟨0, 1, 2, 1⟩ ∧
      divide 1 2 4 2 = ⟨0, 2, 1, 2⟩ ∧
      coefficientStart (IterationState.initial 2 1) (divide 1 2 4 2) = ⟨0, 2, 1⟩ := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.DivisionPhase
