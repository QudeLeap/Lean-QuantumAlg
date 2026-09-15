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
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Fixed-width extended Euclidean semantics and execution paths

This module separates the public XGCD relation from the deterministic
coefficient pair selected by Mathlib.  The public relation asks only for the
GCD, a Bezout equation, and signed representability; `eval` is one executable
choice satisfying that relation.

The extended-Euclidean state machine records every active pre-state actually
visited.  It stops immediately when the leading remainder is zero.  A finite
supremum over the fixed-width input domain gives Components a uniform,
width-derived signed workspace bound without postulating a closed-form bound
on intermediate coefficients.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace NumberTheory
namespace XGCD

/-! ## Public semantics -/

/-- XGCD has the same pair of equal-width natural inputs as total GCD. -/
abbrev Input (width : Nat) := GCD.Input width

/-- The fixed-width GCD together with two signed Bezout coefficients. -/
structure Output (width : Nat) where
  /-- The greatest common divisor. -/
  gcd : Word width
  /-- Coefficient multiplying the left input. -/
  leftCoefficient : BoundedSigned (coefficientWidth width)
  /-- Coefficient multiplying the right input. -/
  rightCoefficient : BoundedSigned (coefficientWidth width)
deriving DecidableEq

/-- The ordinary two's-complement representability interval at one width. -/
def signedRepresentable (signedWidth : Nat) (value : Int) : Prop :=
  -(2 ^ (signedWidth - 1) : Int) ≤ value ∧
    value < (2 ^ (signedWidth - 1) : Int)

/-- The public coefficient interval derived uniformly from the input width. -/
def coefficientRepresentable {width : Nat} (value : Int) : Prop :=
  signedRepresentable (coefficientWidth width) value

/-- Public XGCD correctness.

In particular, this relation does not require the particular coefficient pair
returned by `Nat.gcdA` and `Nat.gcdB`; any representable pair satisfying the
Bezout equation is accepted. -/
def accepts {width : Nat} (input : Input width) (output : Output width) : Prop :=
  output.gcd.val = Nat.gcd input.left.val input.right.val ∧
    (output.gcd.val : Int) =
      (input.left.val : Int) * output.leftCoefficient.toInt +
        (input.right.val : Int) * output.rightCoefficient.toInt ∧
    coefficientRepresentable (width := width)
      output.leftCoefficient.toInt ∧
    coefficientRepresentable (width := width)
      output.rightCoefficient.toInt

/-- One deterministic XGCD implementation, using Mathlib's selected pair. -/
def eval {width : Nat} (input : Input width) : Output width where
  gcd := GCD.eval input
  leftCoefficient :=
    BoundedSigned.ofInt (coefficientWidth width)
      (Nat.gcdA input.left.val input.right.val)
  rightCoefficient :=
    BoundedSigned.ofInt (coefficientWidth width)
      (Nat.gcdB input.left.val input.right.val)

@[simp] theorem xgcdEval_gcd_val {width : Nat} (input : Input width) :
    (eval input).gcd.val = Nat.gcd input.left.val input.right.val :=
  rfl

@[simp] theorem xgcdEval_leftCoefficient_toInt {width : Nat}
    (input : Input width) :
    (eval input).leftCoefficient.toInt =
      Nat.gcdA input.left.val input.right.val := by
  simpa [eval] using
    gcdA_toInt_ofInt_coefficientWidth input.left input.right

@[simp] theorem xgcdEval_rightCoefficient_toInt {width : Nat}
    (input : Input width) :
    (eval input).rightCoefficient.toInt =
      Nat.gcdB input.left.val input.right.val := by
  simpa [eval] using
    gcdB_toInt_ofInt_coefficientWidth input.left input.right

/-- The deterministic implementation satisfies the normalization-independent
public relation. -/
theorem xgcdEval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) := by
  constructor
  · rfl
  constructor
  · rw [xgcdEval_gcd_val, xgcdEval_leftCoefficient_toInt,
      xgcdEval_rightCoefficient_toInt]
    exact Nat.gcd_eq_gcd_ab input.left.val input.right.val
  constructor
  · exact
      ⟨BoundedSigned.lowerBound (eval input).leftCoefficient,
        BoundedSigned.upperBound (eval input).leftCoefficient⟩
  · exact
      ⟨BoundedSigned.lowerBound (eval input).rightCoefficient,
        BoundedSigned.upperBound (eval input).rightCoefficient⟩

/-! ## Executable extended-Euclidean state machine -/

/-- A Euclidean remainder pair and its two pairs of Bezout coefficients.

`first` is the next divisor and `second` is the preceding divisor.  Each
remainder is represented as a linear combination of the original inputs. -/
structure State where
  /-- The current divisor, whose zero value terminates execution. -/
  first : Nat
  /-- The preceding divisor, or the GCD after termination. -/
  second : Nat
  /-- Coefficient of the original left input in `first`. -/
  firstLeftCoefficient : Int
  /-- Coefficient of the original right input in `first`. -/
  firstRightCoefficient : Int
  /-- Coefficient of the original left input in `second`. -/
  secondLeftCoefficient : Int
  /-- Coefficient of the original right input in `second`. -/
  secondRightCoefficient : Int
deriving Repr, DecidableEq

attribute [nolint unusedArguments] instReprState instReprState.repr

namespace State

/-- Whether this state admits one genuine extended-Euclidean step. -/
def active (state : State) : Prop :=
  state.first ≠ 0

/-- The natural quotient used by the next extended-Euclidean update. -/
def quotient (state : State) : Nat :=
  state.second / state.first

/-- Forget coefficients and retain the underlying Euclidean state. -/
def toEuclid (state : State) : Euclid.State where
  first := state.first
  second := state.second

/-- The GCD carried by a finished state. -/
def resultGCD (state : State) : Nat :=
  state.second

/-- The left Bezout coefficient carried by a finished state. -/
def resultLeftCoefficient (state : State) : Int :=
  state.secondLeftCoefficient

/-- The right Bezout coefficient carried by a finished state. -/
def resultRightCoefficient (state : State) : Int :=
  state.secondRightCoefficient

/-- Finished remainder and both finished coefficients as Mathlib's XGCD tuple. -/
def resultTriple (state : State) : Nat × Int × Int :=
  (state.resultGCD,
    (state.resultLeftCoefficient, state.resultRightCoefficient))

/-- Both remainders are linear combinations of the original inputs. -/
def represents (state : State) (left right : Nat) : Prop :=
  (state.first : Int) =
      (left : Int) * state.firstLeftCoefficient +
        (right : Int) * state.firstRightCoefficient ∧
    (state.second : Int) =
      (left : Int) * state.secondLeftCoefficient +
        (right : Int) * state.secondRightCoefficient

/-- Largest magnitude among all four coefficients in one state. -/
def coefficientMagnitude (state : State) : Nat :=
  max
    (max state.firstLeftCoefficient.natAbs
      state.firstRightCoefficient.natAbs)
    (max state.secondLeftCoefficient.natAbs
      state.secondRightCoefficient.natAbs)

theorem firstLeftCoefficient_natAbs_le_coefficientMagnitude (state : State) :
    state.firstLeftCoefficient.natAbs ≤ state.coefficientMagnitude :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem firstRightCoefficient_natAbs_le_coefficientMagnitude (state : State) :
    state.firstRightCoefficient.natAbs ≤ state.coefficientMagnitude :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)

theorem secondLeftCoefficient_natAbs_le_coefficientMagnitude (state : State) :
    state.secondLeftCoefficient.natAbs ≤ state.coefficientMagnitude :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem secondRightCoefficient_natAbs_le_coefficientMagnitude (state : State) :
    state.secondRightCoefficient.natAbs ≤ state.coefficientMagnitude :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

end State

/-- One total extended-Euclidean remainder and coefficient update. -/
def step (state : State) : State where
  first := state.second % state.first
  second := state.first
  firstLeftCoefficient :=
    state.secondLeftCoefficient -
      (state.quotient : Int) * state.firstLeftCoefficient
  firstRightCoefficient :=
    state.secondRightCoefficient -
      (state.quotient : Int) * state.firstRightCoefficient
  secondLeftCoefficient := state.firstLeftCoefficient
  secondRightCoefficient := state.firstRightCoefficient

/-- Run at most `fuel` active extended-Euclidean steps, stopping on zero. -/
def run : Nat → State → State
  | 0, state => state
  | Nat.succ fuel, state =>
      if state.first = 0 then state else run fuel (step state)

/-- Active pre-states of exactly the extended-Euclidean steps performed. -/
def path : Nat → State → List State
  | 0, _state => []
  | Nat.succ fuel, state =>
      if state.first = 0 then [] else state :: path fuel (step state)

/-- Number of genuine extended-Euclidean steps represented by a path. -/
def activeStepCount (fuel : Nat) (state : State) : Nat :=
  (path fuel state).length

@[simp] theorem xgcdStep_toEuclid (state : State) :
    (step state).toEuclid = Euclid.step state.toEuclid :=
  rfl

/-- Forgetting coefficients commutes with the entire fuelled run. -/
theorem xgcdRun_toEuclid (fuel : Nat) (state : State) :
    (run fuel state).toEuclid = Euclid.run fuel state.toEuclid := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [run, Euclid.run]
      change
        (if state.first = 0 then state else run fuel (step state)).toEuclid =
          if state.first = 0 then state.toEuclid
          else Euclid.run fuel (Euclid.step state.toEuclid)
      by_cases finished : state.first = 0
      · rw [if_pos finished, if_pos finished]
      · rw [if_neg finished, if_neg finished]
        rw [inductionHypothesis (step state), xgcdStep_toEuclid]

/-- Forgetting coefficients maps the actual XGCD path to the GCD path. -/
theorem xgcdPath_toEuclid (fuel : Nat) (state : State) :
    (path fuel state).map State.toEuclid =
      Euclid.path fuel state.toEuclid := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [path, Euclid.path]
      change
        (if state.first = 0 then [] else state :: path fuel (step state)).map
            State.toEuclid =
          if state.first = 0 then []
          else state.toEuclid ::
            Euclid.path fuel (Euclid.step state.toEuclid)
      by_cases finished : state.first = 0
      · rw [if_pos finished, if_pos finished]
        rfl
      · rw [if_neg finished, if_neg finished, List.map_cons]
        rw [inductionHypothesis (step state), xgcdStep_toEuclid]

/-- The extended path and its underlying Euclidean path have equal length. -/
theorem xgcdPath_length_eq_euclidPath_length (fuel : Nat) (state : State) :
    (path fuel state).length =
      (Euclid.path fuel state.toEuclid).length := by
  have mapped := congrArg List.length (xgcdPath_toEuclid fuel state)
  simpa using mapped

/-- Every recorded extended state is an actual active pre-state. -/
theorem xgcdPath_mem_active {fuel : Nat} {state visited : State}
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

/-- An extended path cannot exceed its supplied fuel. -/
theorem xgcdPath_length_le_fuel (fuel : Nat) (state : State) :
    (path fuel state).length ≤ fuel := by
  rw [xgcdPath_length_eq_euclidPath_length]
  exact Euclid.euclidPath_length_le_fuel fuel state.toEuclid

@[simp] theorem xgcdActiveStepCount_eq_path_length
    (fuel : Nat) (state : State) :
    activeStepCount fuel state = (path fuel state).length :=
  rfl

theorem xgcdActiveStepCount_le_fuel (fuel : Nat) (state : State) :
    activeStepCount fuel state ≤ fuel :=
  xgcdPath_length_le_fuel fuel state

/-- A sufficient Euclidean budget also terminates the extended run. -/
theorem xgcdRun_first_eq_zero_of_first_lt (fuel : Nat) (state : State)
    (firstRange : state.first < fuel) :
    (run fuel state).first = 0 := by
  exact
    (congrArg Euclid.State.first (xgcdRun_toEuclid fuel state)).trans
      (Euclid.euclidRun_first_eq_zero_of_first_lt
        fuel state.toEuclid firstRange)

/-- A sufficient run carries the GCD in its second remainder. -/
theorem xgcdRun_result_eq_gcd_of_first_lt (fuel : Nat) (state : State)
    (firstRange : state.first < fuel) :
    (run fuel state).resultGCD = Nat.gcd state.first state.second := by
  calc
    (run fuel state).resultGCD =
        (Euclid.run fuel state.toEuclid).result := by
      exact congrArg Euclid.State.second (xgcdRun_toEuclid fuel state)
    _ = Nat.gcd state.toEuclid.first state.toEuclid.second :=
      Euclid.euclidRun_result_eq_gcd_of_first_lt
        fuel state.toEuclid firstRange
    _ = Nat.gcd state.first state.second := rfl

/-- One extended step preserves both linear-combination equations. -/
theorem xgcdStep_represents {state : State} {left right : Nat}
    (representation : state.represents left right) :
    (step state).represents left right := by
  rcases representation with ⟨firstEquation, secondEquation⟩
  have divisionEquation :
      ((state.second % state.first : Nat) : Int) +
          (state.first : Int) *
            ((state.second / state.first : Nat) : Int) =
        (state.second : Int) := by
    exact_mod_cast Nat.mod_add_div state.second state.first
  constructor
  · change
      ((state.second % state.first : Nat) : Int) =
        (left : Int) *
            (state.secondLeftCoefficient -
              (state.quotient : Int) * state.firstLeftCoefficient) +
          (right : Int) *
            (state.secondRightCoefficient -
              (state.quotient : Int) * state.firstRightCoefficient)
    calc
      ((state.second % state.first : Nat) : Int) =
          (state.second : Int) -
            ((state.second / state.first : Nat) : Int) *
              (state.first : Int) := by
        apply (eq_sub_iff_add_eq).2
        simpa [mul_comm] using divisionEquation
      _ =
          (left : Int) *
              (state.secondLeftCoefficient -
                (state.quotient : Int) * state.firstLeftCoefficient) +
            (right : Int) *
              (state.secondRightCoefficient -
                (state.quotient : Int) * state.firstRightCoefficient) := by
        rw [firstEquation, secondEquation]
        simp only [State.quotient]
        ring
  · exact firstEquation

/-- Every fuelled run preserves both linear-combination equations. -/
theorem xgcdRun_represents (fuel : Nat) {state : State} {left right : Nat}
    (representation : state.represents left right) :
    (run fuel state).represents left right := by
  induction fuel generalizing state with
  | zero => exact representation
  | succ fuel inductionHypothesis =>
      by_cases finished : state.first = 0
      · simpa [run, finished] using representation
      · simp only [run, finished, if_false]
        exact inductionHypothesis (xgcdStep_represents representation)

/-- A fuelled run that reached zero returns exactly the tuple selected by
Mathlib's extended-Euclidean recurrence from the same starting state. -/
theorem xgcdRun_resultTriple_eq_xgcdAux (fuel : Nat) (state : State)
    (finished : (run fuel state).first = 0) :
    (run fuel state).resultTriple =
      Nat.xgcdAux state.first state.firstLeftCoefficient
        state.firstRightCoefficient state.second
        state.secondLeftCoefficient state.secondRightCoefficient := by
  induction fuel generalizing state with
  | zero =>
      have firstZero : state.first = 0 := by
        simpa [run] using finished
      simp [run, State.resultTriple, State.resultGCD,
        State.resultLeftCoefficient, State.resultRightCoefficient, firstZero]
  | succ fuel inductionHypothesis =>
      by_cases firstZero : state.first = 0
      · simp [run, State.resultTriple, State.resultGCD,
          State.resultLeftCoefficient, State.resultRightCoefficient, firstZero]
      · have tailFinished : (run fuel (step state)).first = 0 := by
          simpa [run, firstZero] using finished
        calc
          (run (Nat.succ fuel) state).resultTriple =
              (run fuel (step state)).resultTriple := by
            simp [run, firstZero]
          _ =
              Nat.xgcdAux (step state).first
                (step state).firstLeftCoefficient
                (step state).firstRightCoefficient (step state).second
                (step state).secondLeftCoefficient
                (step state).secondRightCoefficient :=
            inductionHypothesis (step state) tailFinished
          _ =
              Nat.xgcdAux state.first state.firstLeftCoefficient
                state.firstRightCoefficient state.second
                state.secondLeftCoefficient state.secondRightCoefficient := by
            symm
            simpa [step, State.quotient] using
              (Nat.xgcdAux_rec
                (r := state.first)
                (s := state.firstLeftCoefficient)
                (t := state.firstRightCoefficient)
                (r' := state.second)
                (s' := state.secondLeftCoefficient)
                (t' := state.secondRightCoefficient)
                (Nat.zero_lt_of_ne_zero firstZero))

/-! ## Fixed-width path and coefficient bounds -/

/-- Initial coefficient basis for one fixed-width input pair. -/
def initialState {width : Nat} (input : Input width) : State where
  first := input.left.val
  second := input.right.val
  firstLeftCoefficient := 1
  firstRightCoefficient := 0
  secondLeftCoefficient := 0
  secondRightCoefficient := 1

/-- Actual unpadded XGCD path under the linear width-derived budget. -/
def trace {width : Nat} (input : Input width) : List State :=
  path (Euclid.gcdFuel width) (initialState input)

/-- Final XGCD state under the linear width-derived budget. -/
def finalState {width : Nat} (input : Input width) : State :=
  run (Euclid.gcdFuel width) (initialState input)

/-- Number of active extended-Euclidean steps actually taken. -/
def traceStepCount {width : Nat} (input : Input width) : Nat :=
  (trace input).length

/-- States whose coefficients must be representable during one execution.

This list is used only to define a workspace bound.  The resource trace remains
`trace`, so the finished state is not charged as an extra executed step. -/
def executionStates {width : Nat} (input : Input width) : List State :=
  trace input ++ [finalState input]

theorem xgcdInitialState_represents {width : Nat} (input : Input width) :
    (initialState input).represents input.left.val input.right.val := by
  change
    (input.left.val : Int) =
        (input.left.val : Int) * 1 + (input.right.val : Int) * 0 ∧
      (input.right.val : Int) =
        (input.left.val : Int) * 0 + (input.right.val : Int) * 1
  constructor <;> ring

theorem xgcdInitialState_first_lt_pow {width : Nat}
    (input : Input width) :
    (initialState input).first < 2 ^ width := by
  exact input.left.isLt

/-- The linear Euclidean budget also terminates the extended recurrence. -/
theorem xgcdRun_first_eq_zero_of_first_lt_pow (width : Nat) (state : State)
    (firstRange : state.first < 2 ^ width) :
    (run (Euclid.gcdFuel width) state).first = 0 := by
  exact
    (congrArg Euclid.State.first
      (xgcdRun_toEuclid (Euclid.gcdFuel width) state)).trans
      (Euclid.euclidRun_first_eq_zero_of_first_lt_pow
        width state.toEuclid firstRange)

/-- The width-derived budget always reaches a finished XGCD state. -/
theorem xgcdFinalState_first_eq_zero {width : Nat} (input : Input width) :
    (finalState input).first = 0 := by
  exact xgcdRun_first_eq_zero_of_first_lt_pow width (initialState input)
    (xgcdInitialState_first_lt_pow input)

/-- The finished executable recurrence selects exactly Mathlib's deterministic
GCD and coefficient tuple. -/
theorem xgcdFinalState_resultTriple_eq_selected {width : Nat}
    (input : Input width) :
    (finalState input).resultTriple =
      (Nat.gcd input.left.val input.right.val,
        (Nat.gcdA input.left.val input.right.val,
          Nat.gcdB input.left.val input.right.val)) := by
  calc
    (finalState input).resultTriple =
        Nat.xgcdAux input.left.val 1 0 input.right.val 0 1 := by
      simpa [finalState, initialState] using
        xgcdRun_resultTriple_eq_xgcdAux
          (Euclid.gcdFuel width) (initialState input)
          (xgcdFinalState_first_eq_zero input)
    _ =
        (Nat.gcd input.left.val input.right.val,
          Nat.xgcd input.left.val input.right.val) :=
      Nat.xgcdAux_val input.left.val input.right.val
    _ =
        (Nat.gcd input.left.val input.right.val,
          (Nat.gcdA input.left.val input.right.val,
            Nat.gcdB input.left.val input.right.val)) := by
      rw [Nat.xgcd_val]

@[simp] theorem xgcdFinalState_resultLeftCoefficient_eq_gcdA {width : Nat}
    (input : Input width) :
    (finalState input).resultLeftCoefficient =
      Nat.gcdA input.left.val input.right.val := by
  exact congrArg (fun result : Nat × Int × Int => result.2.1)
    (xgcdFinalState_resultTriple_eq_selected input)

@[simp] theorem xgcdFinalState_resultRightCoefficient_eq_gcdB {width : Nat}
    (input : Input width) :
    (finalState input).resultRightCoefficient =
      Nat.gcdB input.left.val input.right.val := by
  exact congrArg (fun result : Nat × Int × Int => result.2.2)
    (xgcdFinalState_resultTriple_eq_selected input)

/-- The finished extended state carries the same GCD as `eval`. -/
theorem xgcdFinalState_resultGCD_eq_eval {width : Nat}
    (input : Input width) :
    (finalState input).resultGCD = (eval input).gcd.val := by
  have finished := xgcdFinalState_first_eq_zero input
  calc
    (finalState input).resultGCD =
        Nat.gcd (finalState input).first (finalState input).second := by
      simp [State.resultGCD, finished]
    _ = Nat.gcd input.left.val input.right.val := by
      calc
        Nat.gcd (finalState input).first (finalState input).second =
            Nat.gcd
              (Euclid.run (Euclid.gcdFuel width)
                (initialState input).toEuclid).first
              (Euclid.run (Euclid.gcdFuel width)
                (initialState input).toEuclid).second := by
          exact congrArg
            (fun state : Euclid.State => Nat.gcd state.first state.second)
            (xgcdRun_toEuclid (Euclid.gcdFuel width)
              (initialState input))
        _ = Nat.gcd (initialState input).first
              (initialState input).second :=
          Euclid.euclidRun_gcd (Euclid.gcdFuel width)
            (initialState input).toEuclid
        _ = Nat.gcd input.left.val input.right.val := rfl
    _ = (eval input).gcd.val := by
      simp [eval]

/-- The final state's coefficients remain a genuine Bezout representation. -/
theorem xgcdFinalState_represents {width : Nat} (input : Input width) :
    (finalState input).represents input.left.val input.right.val := by
  exact xgcdRun_represents (Euclid.gcdFuel width)
    (xgcdInitialState_represents input)

/-- The actual extended recurrence finishes with a valid Bezout equation. -/
theorem xgcdFinalState_bezout {width : Nat} (input : Input width) :
    (Nat.gcd input.left.val input.right.val : Int) =
      (input.left.val : Int) *
          (finalState input).resultLeftCoefficient +
        (input.right.val : Int) *
          (finalState input).resultRightCoefficient := by
  have representation := (xgcdFinalState_represents input).2
  have result :
      (finalState input).second =
        Nat.gcd input.left.val input.right.val := by
    simpa [State.resultGCD] using
      xgcdFinalState_resultGCD_eq_eval input
  calc
    (Nat.gcd input.left.val input.right.val : Int) =
        ((finalState input).second : Int) := by
      exact_mod_cast result.symm
    _ =
        (input.left.val : Int) *
            (finalState input).resultLeftCoefficient +
          (input.right.val : Int) *
            (finalState input).resultRightCoefficient :=
      representation

@[simp] theorem xgcdTraceStepCount_eq_trace_length {width : Nat}
    (input : Input width) :
    traceStepCount input = (trace input).length :=
  rfl

/-- Every trace entry is an active state, with no finished padding. -/
theorem xgcdTrace_mem_active {width : Nat} (input : Input width)
    {state : State} (membership : state ∈ trace input) : state.active := by
  exact xgcdPath_mem_active membership

/-- The actual XGCD trace has the linear width-derived length bound. -/
theorem xgcdTrace_length_le_gcdFuel {width : Nat} (input : Input width) :
    (trace input).length ≤ Euclid.gcdFuel width := by
  exact xgcdPath_length_le_fuel
    (Euclid.gcdFuel width) (initialState input)

theorem xgcdTraceStepCount_le_gcdFuel {width : Nat}
    (input : Input width) :
    traceStepCount input ≤ Euclid.gcdFuel width :=
  xgcdTrace_length_le_gcdFuel input

/-- Maximum coefficient magnitude in a concrete finite state list. -/
def stateListCoefficientMagnitude (states : List State) : Nat :=
  (states.map State.coefficientMagnitude).foldr max 0

theorem coefficientMagnitude_le_stateListCoefficientMagnitude
    {states : List State} {state : State} (membership : state ∈ states) :
    state.coefficientMagnitude ≤ stateListCoefficientMagnitude states := by
  apply List.le_max_of_le
  · exact List.mem_map.mpr ⟨state, membership, rfl⟩
  · exact le_rfl

/-- Uniform maximum coefficient magnitude over every fixed-width execution.

This is a computable finite maximum: both the input domain and every fuelled
execution are finite. -/
def executionCoefficientBound (width : Nat) : Nat :=
  Finset.univ.sup fun input : Word width × Word width =>
    stateListCoefficientMagnitude
      (executionStates ({ left := input.1, right := input.2 } : Input width))

/-- Signed workspace width sufficient for every visited and final coefficient. -/
def executionCoefficientWidth (width : Nat) : Nat :=
  max (coefficientWidth width)
    (Nat.size (executionCoefficientBound width) + 2)

/-- The execution workspace is never narrower than the public coefficient
encoding, so final two's-complement words can be narrowed without sign
extension. -/
theorem coefficientWidth_le_executionCoefficientWidth (width : Nat) :
    coefficientWidth width ≤ executionCoefficientWidth width := by
  exact Nat.le_max_left _ _

theorem executionCoefficientWidth_pos (width : Nat) :
    0 < executionCoefficientWidth width := by
  exact (coefficientWidth_pos width).trans_le
    (coefficientWidth_le_executionCoefficientWidth width)

/-- Every coefficient in every visited or final state is below the uniform
width-derived execution bound. -/
theorem xgcdExecutionState_coefficientMagnitude_le_bound {width : Nat}
    (input : Input width) {state : State}
    (membership : state ∈ executionStates input) :
    state.coefficientMagnitude ≤ executionCoefficientBound width := by
  have localBound :
      state.coefficientMagnitude ≤
        stateListCoefficientMagnitude (executionStates input) :=
    coefficientMagnitude_le_stateListCoefficientMagnitude membership
  have inputBound :
      stateListCoefficientMagnitude (executionStates input) ≤
        executionCoefficientBound width := by
    rcases input with ⟨left, right⟩
    unfold executionCoefficientBound
    exact Finset.le_sup
      (s := (Finset.univ : Finset (Word width × Word width)))
      (f := fun input : Word width × Word width =>
        stateListCoefficientMagnitude
          (executionStates
            ({ left := input.1, right := input.2 } : Input width)))
      (Finset.mem_univ (left, right))
  exact localBound.trans inputBound

theorem xgcdTrace_coefficientMagnitude_le_bound {width : Nat}
    (input : Input width) {state : State} (membership : state ∈ trace input) :
    state.coefficientMagnitude ≤ executionCoefficientBound width := by
  apply xgcdExecutionState_coefficientMagnitude_le_bound input
  simp [executionStates, membership]

theorem xgcdFinalState_coefficientMagnitude_le_bound {width : Nat}
    (input : Input width) :
    (finalState input).coefficientMagnitude ≤
      executionCoefficientBound width := by
  apply xgcdExecutionState_coefficientMagnitude_le_bound input
  simp [executionStates]

/-- The execution coefficient bound fits strictly inside the positive capacity
of the public execution workspace width. -/
theorem executionCoefficientBound_lt_signedCapacity (width : Nat) :
    executionCoefficientBound width <
      2 ^ (executionCoefficientWidth width - 1) := by
  have bound_lt_size :
      executionCoefficientBound width <
        2 ^ Nat.size (executionCoefficientBound width) :=
    Nat.lt_size_self _
  have size_capacity_le :
      2 ^ Nat.size (executionCoefficientBound width) ≤
        2 ^ (Nat.size (executionCoefficientBound width) + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
  have originalCapacity :
      executionCoefficientBound width <
        2 ^ (Nat.size (executionCoefficientBound width) + 1) :=
    bound_lt_size.trans_le size_capacity_le
  have exponentLe :
      Nat.size (executionCoefficientBound width) + 1 ≤
        executionCoefficientWidth width - 1 := by
    have widthLe : Nat.size (executionCoefficientBound width) + 2 ≤
        executionCoefficientWidth width := by
      exact Nat.le_max_right _ _
    omega
  exact originalCapacity.trans_le
    (Nat.pow_le_pow_right (by decide) exponentLe)

/-- Any integer below the execution bound lies in the corresponding signed
workspace range. -/
theorem int_in_executionCoefficientRange_of_natAbs_le {width : Nat}
    {value : Int}
    (magnitude : value.natAbs ≤ executionCoefficientBound width) :
    signedRepresentable (executionCoefficientWidth width) value := by
  have capacity := executionCoefficientBound_lt_signedCapacity width
  have magnitude_lt :
      value.natAbs < 2 ^ (executionCoefficientWidth width - 1) :=
    magnitude.trans_lt capacity
  have upperNat :
      (value.natAbs : Int) <
        (2 ^ (executionCoefficientWidth width - 1) : Nat) :=
    Int.ofNat_lt.mpr magnitude_lt
  have capacityCast :
      ((2 ^ (executionCoefficientWidth width - 1) : Nat) : Int) =
        (2 ^ (executionCoefficientWidth width - 1) : Int) := by
    norm_num
  unfold signedRepresentable
  rw [← capacityCast]
  by_cases nonnegative : 0 ≤ value
  · have absEq : (value.natAbs : Int) = value :=
      Int.natAbs_of_nonneg nonnegative
    rw [absEq] at upperNat
    constructor
    · have capacityNonnegative :
          (0 : Int) ≤
            (2 ^ (executionCoefficientWidth width - 1) : Nat) := by
        positivity
      omega
    · exact upperNat
  · have nonpositive : value ≤ 0 := Int.le_of_not_le nonnegative
    have absEq : (value.natAbs : Int) = -value :=
      Int.ofNat_natAbs_of_nonpos nonpositive
    rw [absEq] at upperNat
    constructor
    · omega
    · have capacityPositive :
          (0 : Int) <
            (2 ^ (executionCoefficientWidth width - 1) : Nat) := by
        positivity
      omega

/-- Every coefficient in a visited or final state fits the uniform signed
workspace width. -/
theorem xgcdExecutionState_coefficients_representable {width : Nat}
    (input : Input width) {state : State}
    (membership : state ∈ executionStates input) :
    signedRepresentable (executionCoefficientWidth width)
        state.firstLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width)
        state.firstRightCoefficient ∧
      signedRepresentable (executionCoefficientWidth width)
        state.secondLeftCoefficient ∧
      signedRepresentable (executionCoefficientWidth width)
        state.secondRightCoefficient := by
  have stateBound :=
    xgcdExecutionState_coefficientMagnitude_le_bound input membership
  exact
    ⟨int_in_executionCoefficientRange_of_natAbs_le
        ((State.firstLeftCoefficient_natAbs_le_coefficientMagnitude state).trans
          stateBound),
      int_in_executionCoefficientRange_of_natAbs_le
        ((State.firstRightCoefficient_natAbs_le_coefficientMagnitude state).trans
          stateBound),
      int_in_executionCoefficientRange_of_natAbs_le
        ((State.secondLeftCoefficient_natAbs_le_coefficientMagnitude state).trans
          stateBound),
      int_in_executionCoefficientRange_of_natAbs_le
        ((State.secondRightCoefficient_natAbs_le_coefficientMagnitude state).trans
          stateBound)⟩

end XGCD
end NumberTheory

end ClassicalAlgorithms
end QuantumAlg

end
