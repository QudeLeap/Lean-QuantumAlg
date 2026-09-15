/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.Classical.Modular.Additive
import all QuantumAlg.Util.Classical.NumberTheory.Basic
import all QuantumAlg.Util.Classical.NumberTheory.Checked

/-!
# Total fixed-width GCD and its Euclidean execution path

This module separates total mathematical GCD semantics from the executable
Euclidean state machine used to realize them.  A fuelled execution records only
states at which one remainder step is actually taken.  It stops immediately at
the first zero leading remainder, so the trace contains no padded iterations.

The common word-width modulus bounds stored values, while a separate linear
`Euclid.gcdFuel` schedule finishes the executable recurrence by the standard
two-step bit-length decrease.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace NumberTheory

/-! ## Executable Euclidean state machine -/

namespace Euclid

/-- One state of Euclid's remainder recurrence.

The first coordinate is the next divisor.  A state is finished exactly when
that coordinate is zero, at which point the second coordinate is the GCD. -/
structure State where
  /-- The current divisor, whose zero value terminates execution. -/
  first : Nat
  /-- The preceding divisor, or the result after termination. -/
  second : Nat
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprState instReprState.repr

namespace State

/-- Whether this state admits one genuine Euclidean remainder step. -/
def active (state : State) : Prop :=
  state.first ≠ 0

/-- The mathematical result exposed by a finished state. -/
def result (state : State) : Nat :=
  state.second

end State

/-- One total remainder update.

Executions call this function only for active states; keeping the function
total makes the state transition directly executable. -/
def step (state : State) : State where
  first := state.second % state.first
  second := state.first

/-- Run at most `fuel` active Euclidean steps and stop immediately on zero. -/
def run : Nat → State → State
  | 0, state => state
  | Nat.succ fuel, state =>
      if state.first = 0 then state else run fuel (step state)

/-- The pre-state of every Euclidean step that was actually executed.

No state is appended after termination, and exhausted fuel does not manufacture
padding steps. -/
def path : Nat → State → List State
  | 0, _state => []
  | Nat.succ fuel, state =>
      if state.first = 0 then [] else state :: path fuel (step state)

/-- Number of genuine active steps represented by a fuelled path. -/
def activeStepCount (fuel : Nat) (state : State) : Nat :=
  (path fuel state).length

/-- One remainder step preserves the mathematical GCD. -/
theorem euclidStep_gcd (state : State) :
    Nat.gcd state.first state.second =
      Nat.gcd (step state).first (step state).second := by
  simpa [step] using Nat.gcd_rec state.first state.second

/-- The leading coordinate strictly decreases at every active step. -/
theorem euclidStep_first_lt (state : State) (active : state.active) :
    (step state).first < state.first := by
  exact Nat.mod_lt state.second (Nat.zero_lt_of_ne_zero active)

/-- Fuelled execution preserves the initial mathematical GCD. -/
theorem euclidRun_gcd (fuel : Nat) (state : State) :
    Nat.gcd (run fuel state).first (run fuel state).second =
      Nat.gcd state.first state.second := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      by_cases finished : state.first = 0
      · simp [run, finished]
      · simp only [run, finished, if_false]
        rw [inductionHypothesis (step state)]
        exact (euclidStep_gcd state).symm

/-- Once a fuelled run has reached a finished state, its result is the
initial mathematical GCD.  This form separates semantic correctness from
the particular schedule used to establish termination. -/
theorem euclidRun_result_eq_gcd_of_finished (fuel : Nat) (state : State)
    (finished : (run fuel state).first = 0) :
    (run fuel state).result = Nat.gcd state.first state.second := by
  calc
    (run fuel state).result =
        Nat.gcd (run fuel state).first (run fuel state).second := by
      simp [State.result, finished]
    _ = Nat.gcd state.first state.second := euclidRun_gcd fuel state

/-- Fuel larger than the leading coordinate always reaches a finished state. -/
theorem euclidRun_first_eq_zero_of_first_lt :
    ∀ (fuel : Nat) (state : State),
      state.first < fuel → (run fuel state).first = 0 := by
  intro fuel
  induction fuel with
  | zero =>
      intro state firstRange
      exact (Nat.not_lt_zero state.first firstRange).elim
  | succ fuel inductionHypothesis =>
      intro state firstRange
      by_cases finished : state.first = 0
      · simp [run, finished]
      · have stepDecrease : (step state).first < state.first :=
          euclidStep_first_lt state finished
        have stateLeFuel : state.first ≤ fuel :=
          Nat.le_of_lt_succ firstRange
        have stepRange : (step state).first < fuel :=
          Nat.lt_of_lt_of_le stepDecrease stateLeFuel
        simp only [run, finished, if_false]
        exact inductionHypothesis (step state) stepRange

/-- Two genuine Euclidean remainder steps reduce a leading coordinate below
any threshold whose double strictly bounds the original coordinate.  This is
the bit-length argument behind the linear fixed schedule used by `GCD` below:
if the first remainder is already small we are done, while a large first
remainder forces the next quotient to be one and hence the next remainder to
be the complementary small difference. -/
theorem euclidStep_step_first_lt_of_first_lt_add
    (state : State) (bound : Nat)
    (firstBound : state.first < bound + bound)
    (active : state.first ≠ 0) (stepActive : (step state).first ≠ 0) :
    (step (step state)).first < bound := by
  have firstRemainderLt : (step state).first < state.first :=
    euclidStep_first_lt state active
  by_cases remainderSmall : (step state).first ≤ bound
  · exact (euclidStep_first_lt (step state) stepActive).trans_le
      remainderSmall
  · have boundLtRemainder : bound < (step state).first :=
      Nat.lt_of_not_ge remainderSmall
    have remainderLeFirst : (step state).first ≤ state.first :=
      Nat.le_of_lt firstRemainderLt
    have remainderLeFirst' : state.second % state.first ≤ state.first := by
      simpa only [step] using remainderLeFirst
    have boundLtRemainder' : bound < state.second % state.first := by
      simpa only [step] using boundLtRemainder
    change state.first % (state.second % state.first) < bound
    rw [Nat.mod_eq_sub_mod remainderLeFirst']
    rw [Nat.mod_eq_of_lt (by omega)]
    change state.first - (step state).first < bound
    omega

/-- Linear public fuel for Euclid on two `width`-bit words. -/
@[irreducible]
def gcdFuel (width : Nat) : Nat :=
  2 * width + 1

theorem gcdFuel_pos (width : Nat) : 0 < gcdFuel width := by
  simp [gcdFuel]

/-- `2 * width + 1` rounds finish every Euclidean state whose leading
coordinate is below `2^width`.  Unlike the older value-range fuel, this is
polynomial in the encoded bit width. -/
theorem euclidRun_first_eq_zero_of_first_lt_pow :
    ∀ (width : Nat) (state : State), state.first < 2 ^ width →
      (run (gcdFuel width) state).first = 0 := by
  intro width
  induction width with
  | zero =>
      intro state firstBound
      have finished : state.first = 0 := by
        simpa using firstBound
      simp [gcdFuel, run, finished]
  | succ width inductionHypothesis =>
      intro state firstBound
      by_cases finished : state.first = 0
      · simp [gcdFuel, run, finished]
      · let next := step state
        by_cases nextFinished : next.first = 0
        · have fuelEq : gcdFuel width.succ =
              Nat.succ (Nat.succ (gcdFuel width)) := by
            simp [gcdFuel]
            omega
          rw [fuelEq]
          simp [run, finished, next, nextFinished]
        · have doubledBound : state.first < 2 ^ width + 2 ^ width := by
            simpa [pow_succ, Nat.mul_two] using firstBound
          have reduced : (step next).first < 2 ^ width := by
            apply euclidStep_step_first_lt_of_first_lt_add state
              (2 ^ width) doubledBound finished
            simpa only [next] using nextFinished
          have suffix := inductionHypothesis (step next) reduced
          have fuelEq : gcdFuel width.succ =
              Nat.succ (Nat.succ (gcdFuel width)) := by
            simp [gcdFuel]
            omega
          rw [fuelEq]
          simpa only [run, finished, if_false, next, nextFinished] using suffix

/-- A sufficiently fuelled run returns the initial mathematical GCD. -/
theorem euclidRun_result_eq_gcd_of_first_lt (fuel : Nat) (state : State)
    (firstRange : state.first < fuel) :
    (run fuel state).result = Nat.gcd state.first state.second := by
  have finished : (run fuel state).first = 0 :=
    euclidRun_first_eq_zero_of_first_lt fuel state firstRange
  calc
    (run fuel state).result =
        Nat.gcd (run fuel state).first (run fuel state).second := by
      simp [State.result, finished]
    _ = Nat.gcd state.first state.second := euclidRun_gcd fuel state

/-- An actual path can never contain more entries than the supplied fuel. -/
theorem euclidPath_length_le_fuel (fuel : Nat) (state : State) :
    (path fuel state).length ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [path]
  | succ fuel inductionHypothesis =>
      by_cases finished : state.first = 0
      · simp [path, finished]
      · simp only [path, finished, if_false, List.length_cons]
        exact Nat.succ_le_succ (inductionHypothesis (step state))

/-- Every state recorded in the path is an actual active pre-state. -/
theorem euclidPath_mem_active {fuel : Nat} {state visited : State}
    (membership : visited ∈ path fuel state) : visited.active := by
  induction fuel generalizing state with
  | zero => simp [path] at membership
  | succ fuel inductionHypothesis =>
      by_cases finished : state.first = 0
      · simp [path, finished] at membership
      · simp only [path, finished, if_false, List.mem_cons] at membership
        rcases membership with same | later
        · subst visited
          exact finished
        · exact inductionHypothesis later

/-- Active-step count is exactly the length of the unpadded path. -/
@[simp] theorem euclidActiveStepCount_eq_path_length
    (fuel : Nat) (state : State) :
    activeStepCount fuel state = (path fuel state).length :=
  rfl

theorem euclidActiveStepCount_le_fuel (fuel : Nat) (state : State) :
    activeStepCount fuel state ≤ fuel :=
  euclidPath_length_le_fuel fuel state

end Euclid

/-! ## Total fixed-width GCD semantics -/

namespace GCD

/-- Two equal-width operands for total GCD. -/
structure Input (width : Nat) where
  /-- The left operand. -/
  left : Word width
  /-- The right operand. -/
  right : Word width
deriving DecidableEq

/-- A GCD fits in the same width as both input words. -/
abbrev Output (width : Nat) := Word width

/-- Every pair of intrinsically bounded words is a valid total GCD input. -/
@[nolint unusedArguments]
def valid {width : Nat} (_input : Input width) : Prop :=
  True

/-- Standard greatest-common-divisor contract. -/
def accepts {width : Nat} (input : Input width) (output : Output width) : Prop :=
  output.val ∣ input.left.val ∧
    output.val ∣ input.right.val ∧
    ∀ divisor : Nat,
      divisor ∣ input.left.val → divisor ∣ input.right.val →
        divisor ∣ output.val

/-- The GCD of two equal-width words remains within that word width. -/
theorem gcd_lt_euclidFuel {width : Nat} (input : Input width) :
    Nat.gcd input.left.val input.right.val < euclidFuel width := by
  by_cases leftZero : input.left.val = 0
  · rw [leftZero, Nat.gcd_zero_left]
    exact word_val_lt_euclidFuel input.right
  · exact
      (Nat.gcd_le_left input.right.val (Nat.zero_lt_of_ne_zero leftZero)).trans_lt
        (word_val_lt_euclidFuel input.left)

/-- Total fixed-width GCD, including both-zero and one-zero inputs. -/
def eval {width : Nat} (input : Input width) : Output width :=
  ⟨Nat.gcd input.left.val input.right.val,
    gcd_lt_euclidFuel input⟩

@[simp] theorem gcdValid {width : Nat} (input : Input width) :
    valid input :=
  trivial

@[simp] theorem gcdEval_val {width : Nat} (input : Input width) :
    (eval input).val = Nat.gcd input.left.val input.right.val :=
  rfl

theorem gcdEval_dvd_left {width : Nat} (input : Input width) :
    (eval input).val ∣ input.left.val := by
  simpa using Nat.gcd_dvd_left input.left.val input.right.val

theorem gcdEval_dvd_right {width : Nat} (input : Input width) :
    (eval input).val ∣ input.right.val := by
  simpa using Nat.gcd_dvd_right input.left.val input.right.val

theorem gcdEval_greatest {width : Nat} (input : Input width)
    (divisor : Nat) (dividesLeft : divisor ∣ input.left.val)
    (dividesRight : divisor ∣ input.right.val) :
    divisor ∣ (eval input).val := by
  simpa using Nat.dvd_gcd dividesLeft dividesRight

theorem gcdEval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) :=
  ⟨gcdEval_dvd_left input, gcdEval_dvd_right input,
    gcdEval_greatest input⟩

/-- Total semantics when the left input is zero. -/
theorem gcdEval_left_zero {width : Nat} (input : Input width)
    (leftZero : input.left.val = 0) :
    (eval input).val = input.right.val := by
  simp [gcdEval_val, leftZero]

/-- Total semantics when the right input is zero. -/
theorem gcdEval_right_zero {width : Nat} (input : Input width)
    (rightZero : input.right.val = 0) :
    (eval input).val = input.left.val := by
  simp [gcdEval_val, rightZero]

/-- The explicitly admitted both-zero input returns zero. -/
theorem gcdEval_zero_zero {width : Nat} (input : Input width)
    (leftZero : input.left.val = 0) (rightZero : input.right.val = 0) :
    (eval input).val = 0 := by
  rw [gcdEval_left_zero input leftZero, rightZero]

/-- Initial Euclidean state associated with a fixed-width input. -/
def initialState {width : Nat} (input : Input width) : Euclid.State where
  first := input.left.val
  second := input.right.val

/-- Actual unpadded Euclidean path under the linear bit-width schedule. -/
def trace {width : Nat} (input : Input width) : List Euclid.State :=
  Euclid.path (Euclid.gcdFuel width) (initialState input)

/-- Final Euclidean state under the linear bit-width schedule. -/
def finalState {width : Nat} (input : Input width) : Euclid.State :=
  Euclid.run (Euclid.gcdFuel width) (initialState input)

/-- Number of active remainder steps actually taken for this input. -/
def activeStepCount {width : Nat} (input : Input width) : Nat :=
  trace input |>.length

theorem gcdInitialState_first_lt_euclidFuel {width : Nat}
    (input : Input width) :
    (initialState input).first < euclidFuel width := by
  change input.left.val < euclidFuel width
  exact word_val_lt_euclidFuel input.left

/-- The width-derived fuel always reaches the first finished state. -/
theorem gcdFinalState_first_eq_zero {width : Nat} (input : Input width) :
    (finalState input).first = 0 := by
  exact Euclid.euclidRun_first_eq_zero_of_first_lt_pow width
    (initialState input)
    (gcdInitialState_first_lt_euclidFuel input)

/-- The fuelled state machine computes exactly the total GCD semantics. -/
theorem gcdFinalState_result_eq_eval {width : Nat} (input : Input width) :
    (finalState input).result = (eval input).val := by
  have finished :
      (Euclid.run (Euclid.gcdFuel width) (initialState input)).first = 0 := by
    simpa only [finalState] using gcdFinalState_first_eq_zero input
  simpa only [finalState, initialState, gcdEval_val] using
    Euclid.euclidRun_result_eq_gcd_of_finished
      (Euclid.gcdFuel width) (initialState input) finished

/-- The exposed count is definitionally the length of the actual trace. -/
@[simp] theorem gcdActiveStepCount_eq_trace_length {width : Nat}
    (input : Input width) :
    activeStepCount input = (trace input).length :=
  rfl

/-- Every recorded GCD trace state is active; no finished padding is present. -/
theorem gcdTrace_mem_active {width : Nat} (input : Input width)
    {state : Euclid.State} (membership : state ∈ trace input) :
    state.active := by
  exact Euclid.euclidPath_mem_active membership

/-- The actual data-dependent trace shares the linear bit-width bound. -/
theorem gcdTrace_length_le_gcdFuel {width : Nat} (input : Input width) :
    (trace input).length ≤ Euclid.gcdFuel width := by
  exact Euclid.euclidPath_length_le_fuel
    (Euclid.gcdFuel width) (initialState input)

theorem gcdActiveStepCount_le_gcdFuel {width : Nat} (input : Input width) :
    activeStepCount input ≤ Euclid.gcdFuel width :=
  gcdTrace_length_le_gcdFuel input

end GCD

end NumberTheory

end ClassicalAlgorithms
end QuantumAlg

end
