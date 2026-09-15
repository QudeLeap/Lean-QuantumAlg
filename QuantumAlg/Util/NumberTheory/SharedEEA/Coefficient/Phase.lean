/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Exact coefficient-phase microsteps of the shared EEA

The third phase consumes the quotient from its least significant bit,
adds that bit's contribution to the increasing coefficient, clears the
bit, and advances its binary place [LYL+26, sec_EEA/sub_4phase.tex:24-37].
Here `remaining` is the effective quotient suffix and `scale = 2^ℓ` is the
current binary place. Their right/left shifts are exact natural-number
division/multiplication by two. The explicit quotient-bit XOR from
`QuotientBits.consumeBit` is proved to produce zero at every reachable step.

Exactly `Nat.size quotient` such microsteps consume the whole quotient.
Every earlier step still has a nonzero suffix, and the final accumulated
value is precisely the coefficient in `IterationState.step`. Each step and
the entire finite sequence have an explicit left inverse on the invariant
established by the source's original input fold. The final scale is retained;
this module does not freeze a terminal microstate or erase a loop counter.

These are decoded arithmetic and bit-clearing laws. The rotated physical
word representation and complete phase/sign control in
`sec_EEA/sub_regshare.tex:288-315` remain subsequent refinements. No quantum
operation, shared-word capacity, or whole-algorithm cost is claimed here.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.CoefficientPhase

/-- Decoded arithmetic data during quotient consumption. -/
@[ext]
structure State where
  /-- The previous coefficient plus contributions from already consumed bits. -/
  value : Nat
  /-- The not-yet-consumed quotient suffix, with its next bit in the lowest position. -/
  remaining : Nat
  /-- The current binary place, initially one and doubled after every microstep. -/
  scale : Nat
deriving DecidableEq

/-- The actual lowest quotient bit. -/
def lowBit (quotient : Nat) : Bool := decide (quotient % 2 = 1)

/-- The conditional contribution equals the quotient's lowest binary digit times its place. -/
theorem lowBit_contribution (quotient threshold : Nat) :
    (if lowBit quotient then threshold else 0) = quotient % 2 * threshold := by
  have remainderBound := Nat.mod_lt quotient (by decide : 0 < 2)
  by_cases odd : quotient % 2 = 1
  · simp [lowBit, odd]
  · have even : quotient % 2 = 0 := by omega
    simp [lowBit, even]

/-- The recovered Boolean is the actual numerical lowest quotient bit. -/
theorem lowBit_value (quotient : Nat) :
    (if lowBit quotient then 1 else 0) = quotient % 2 := by
  simpa only [Nat.mul_one] using lowBit_contribution quotient 1

/-- One source coefficient microstep, including the quotient and scale shifts. -/
def step (coefficient : Nat) (state : State) : State :=
  ⟨(QuotientBits.consumeBit (state.scale * coefficient)
      (state.value, lowBit state.remaining)).1,
    state.remaining / 2, 2 * state.scale⟩

/-- Recover the previous scale, consumed digit, coefficient, and quotient suffix. -/
def rewind (coefficient : Nat) (state : State) : State :=
  let previousScale := state.scale / 2
  let digit := QuotientBits.readBit (previousScale * coefficient) state.value
  ⟨state.value % (previousScale * coefficient),
    2 * state.remaining + if digit then 1 else 0, previousScale⟩

/-- The source invariant: all accumulated lower contributions fit below the next place. -/
def Below (coefficient : Nat) (state : State) : Prop :=
  state.value < state.scale * coefficient

/-- The actual quotient-bit coordinate is zero after this microstep. -/
theorem step_clears (coefficient : Nat) (state : State) (below : Below coefficient state) :
    (QuotientBits.consumeBit (state.scale * coefficient)
      (state.value, lowBit state.remaining)).2 = false :=
  QuotientBits.consumeBit_clears _ _ _ below

/-- The updated value preserves the low-contribution invariant at the next binary place. -/
theorem step_below (coefficient : Nat) (state : State) (below : Below coefficient state) :
    Below coefficient (step coefficient state) := by
  change (QuotientBits.consumeBit (state.scale * coefficient)
      (state.value, lowBit state.remaining)).1 < (2 * state.scale) * coefficient
  calc
    _ < 2 * (state.scale * coefficient) := QuotientBits.consumeBit_lt_double _ _ _ below
    _ = _ := by ring

/-- The updated arithmetic data reconstruct the actual preceding microstate. -/
theorem rewind_step (coefficient : Nat) (state : State) (below : Below coefficient state) :
    rewind coefficient (step coefficient state) = state := by
  have scaleRecovered : (2 * state.scale) / 2 = state.scale :=
    Nat.mul_div_right state.scale (by decide : 0 < 2)
  have digitRecovered := QuotientBits.readBit_add (state.scale * coefficient)
    state.value (lowBit state.remaining) below
  apply State.ext
  · change (QuotientBits.consumeBit (state.scale * coefficient)
        (state.value, lowBit state.remaining)).1 %
      ((2 * state.scale) / 2 * coefficient) = state.value
    rw [scaleRecovered]
    exact QuotientBits.consumeBit_low _ _ _ below
  · change 2 * (state.remaining / 2) +
      (if QuotientBits.readBit ((2 * state.scale) / 2 * coefficient)
          (state.value + if lowBit state.remaining then state.scale * coefficient else 0)
        then 1 else 0) = state.remaining
    rw [scaleRecovered, digitRecovered, lowBit_value]
    exact Nat.div_add_mod state.remaining 2
  · exact scaleRecovered

/-- The actual microstep is injective on the reachable arithmetic range. -/
theorem step_injective {coefficient : Nat} {left right : State}
    (leftBelow : Below coefficient left) (rightBelow : Below coefficient right)
    (same : step coefficient left = step coefficient right) : left = right := by
  calc
    left = rewind coefficient (step coefficient left) :=
      (rewind_step coefficient left leftBelow).symm
    _ = rewind coefficient (step coefficient right) := congrArg (rewind coefficient) same
    _ = right := rewind_step coefficient right rightBelow

/-- The accumulated contribution plus the still-pending contribution. -/
def total (coefficient : Nat) (state : State) : Nat :=
  state.value + state.remaining * state.scale * coefficient

/-- Each actual bit microstep preserves the complete coefficient value being computed. -/
theorem step_total (coefficient : Nat) (state : State) :
    total coefficient (step coefficient state) = total coefficient state := by
  change state.value + (if lowBit state.remaining then state.scale * coefficient else 0) +
      state.remaining / 2 * (2 * state.scale) * coefficient =
    state.value + state.remaining * state.scale * coefficient
  rw [lowBit_contribution]
  calc
    _ = state.value + (state.remaining % 2 + 2 * (state.remaining / 2)) *
        state.scale * coefficient := by ring
    _ = _ := by rw [Nat.mod_add_div]

/-- A specified number of successive source coefficient microsteps. -/
def run (coefficient : Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => step coefficient (run coefficient count state)

/-- Reverse the same number of actual microsteps, retaining their scale coordinate. -/
def rewindRun (coefficient : Nat) : Nat → State → State
  | 0, state => state
  | count + 1, state => rewindRun coefficient count (rewind coefficient state)

/-- The arithmetic low-part invariant holds at every intermediate microstate. -/
theorem run_below (coefficient count : Nat) (state : State)
    (below : Below coefficient state) : Below coefficient (run coefficient count state) := by
  induction count with
  | zero => exact below
  | succ count inductionHypothesis => exact step_below coefficient _ inductionHypothesis

/-- The complete microstep sequence has an actual left inverse on its reachable range. -/
theorem rewindRun_run (coefficient count : Nat) (state : State)
    (below : Below coefficient state) :
    rewindRun coefficient count (run coefficient count state) = state := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
    change rewindRun coefficient count
      (rewind coefficient (step coefficient (run coefficient count state))) = state
    rw [rewind_step coefficient _ (run_below coefficient count state below)]
    exact inductionHypothesis

/-- The unconsumed quotient is exactly the suffix after the specified right shifts. -/
theorem run_remaining (coefficient count : Nat) (state : State) :
    (run coefficient count state).remaining = state.remaining / 2 ^ count := by
  induction count with
  | zero => simp [run]
  | succ count inductionHypothesis =>
    change (run coefficient count state).remaining / 2 = state.remaining / 2 ^ (count + 1)
    rw [inductionHypothesis, Nat.div_div_eq_div_mul, Nat.pow_succ]

/-- The scale stores the exact binary place after all performed microsteps. -/
theorem run_scale (coefficient count : Nat) (state : State) :
    (run coefficient count state).scale = 2 ^ count * state.scale := by
  induction count with
  | zero => simp [run]
  | succ count inductionHypothesis =>
    change 2 * (run coefficient count state).scale = 2 ^ (count + 1) * state.scale
    rw [inductionHypothesis, Nat.pow_succ]
    ring

/-- The value to be computed is unchanged by the actual finite sequence. -/
theorem run_total (coefficient count : Nat) (state : State) :
    total coefficient (run coefficient count state) = total coefficient state := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
    exact (step_total coefficient (run coefficient count state)).trans inductionHypothesis

/-- The accumulated value contains exactly the consumed low quotient bits from the source. -/
theorem run_value (coefficient count : Nat) (state : State) :
    (run coefficient count state).value =
      state.value + (state.remaining % 2 ^ count) * state.scale * coefficient := by
  have decomposed : state.value + state.remaining * state.scale * coefficient =
      (state.value + (state.remaining % 2 ^ count) * state.scale * coefficient) +
        (state.remaining / 2 ^ count) * (2 ^ count * state.scale) * coefficient := by
    calc
      _ = state.value + (state.remaining % 2 ^ count +
            2 ^ count * (state.remaining / 2 ^ count)) * state.scale * coefficient := by
        rw [Nat.mod_add_div]
      _ = _ := by ring
  have conserved := run_total coefficient count state
  change (run coefficient count state).value + (run coefficient count state).remaining *
      (run coefficient count state).scale * coefficient =
    state.value + state.remaining * state.scale * coefficient at conserved
  rw [run_remaining, run_scale, decomposed] at conserved
  exact Nat.add_right_cancel conserved

/-- Every microstep before the quotient's exact bit length still has a bit to consume. -/
theorem run_active (coefficient count : Nat) (state : State)
    (beforeEnd : count < state.remaining.size) :
    0 < (run coefficient count state).remaining := by
  rw [run_remaining]
  exact Nat.div_pos (Nat.lt_size.mp beforeEnd) (Nat.two_pow_pos count)

/-- Execute exactly the source quotient's effective number of bits. -/
def finish (coefficient : Nat) (state : State) : State :=
  run coefficient state.remaining.size state

/-- The phase ends with all effective quotient bits consumed. -/
theorem finish_remaining (coefficient : Nat) (state : State) :
    (finish coefficient state).remaining = 0 := by
  rw [finish, run_remaining]
  exact Nat.div_eq_of_lt (Nat.lt_size_self state.remaining)

/-- The phase computes the exact whole quotient contribution through its bit microsteps. -/
theorem finish_value (coefficient : Nat) (state : State) :
    (finish coefficient state).value =
      state.value + state.remaining * state.scale * coefficient := by
  have conserved := run_total coefficient state.remaining.size state
  change (finish coefficient state).value + (finish coefficient state).remaining *
      (finish coefficient state).scale * coefficient =
    state.value + state.remaining * state.scale * coefficient at conserved
  simpa only [finish_remaining, Nat.zero_mul, Nat.add_zero] using conserved

/-- Phase-three initialization from the source EEA iteration-boundary coordinates. -/
def start (state : IterationState) : State :=
  ⟨state.previousCoefficient, state.quotient, 1⟩

/-- The reachable macro invariant establishes the actual first microstep's range. -/
theorem start_below (state : IterationState) (valid : state.Admissible) :
    Below state.coefficient (start state) := by
  change state.previousCoefficient < 1 * state.coefficient
  simpa only [Nat.one_mul] using valid.previous_lt

/-- The complete actual coefficient phase agrees with the macro iteration's coefficient. -/
theorem finish_start_coefficient (state : IterationState) :
    (finish state.coefficient (start state)).value = (IterationState.step state).coefficient := by
  rw [finish_value]
  change state.previousCoefficient + state.quotient * 1 * state.coefficient =
    state.previousCoefficient + state.coefficient * state.quotient
  ring

/-- At every real source phase step the suffix is active, its bit clears, and the state recovers. -/
theorem start_progress (state : IterationState) (valid : state.Admissible) (count : Nat)
    (beforeEnd : count < state.quotient.size) :
    let current := run state.coefficient count (start state)
    0 < current.remaining ∧
      (QuotientBits.consumeBit (current.scale * state.coefficient)
        (current.value, lowBit current.remaining)).2 = false ∧
      rewind state.coefficient (step state.coefficient current) = current := by
  have below := run_below state.coefficient count (start state) (start_below state valid)
  exact ⟨run_active state.coefficient count (start state) beforeEnd,
    step_clears state.coefficient _ below, rewind_step state.coefficient _ below⟩

/-- The original positive-residue domain supplies the whole phase's reverse guarantee. -/
theorem folded_start_reversible (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    let initial := IterationState.initial modulus (foldInput modulus input).2
    rewindRun initial.coefficient initial.quotient.size
        (finish initial.coefficient (start initial)) = start initial := by
  exact rewindRun_run _ _ _
    (start_below _ (folded_initial_admissible modulus input positive bounded))

/-- The smallest valid input consumes a zero low bit and then its equality-boundary high bit. -/
theorem smallest_input_two_microsteps :
    start (IterationState.initial 2 1) = ⟨0, 2, 1⟩ ∧
      run 1 1 (start (IterationState.initial 2 1)) = ⟨0, 1, 2⟩ ∧
      finish 1 (start (IterationState.initial 2 1)) = ⟨2, 0, 4⟩ := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.CoefficientPhase
