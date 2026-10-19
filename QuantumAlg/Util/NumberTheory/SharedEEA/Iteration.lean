/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic at shared-register EEA iteration boundaries

The four-phase construction computes one Euclidean quotient, transfers its
bits into the increasing coefficient, and exchanges both remainder and
coefficient pairs [LYL+26, sec_EEA/sub_4phase.tex:8-43]. This module specifies
that complete iteration using natural numbers. Binary division steps, shared
word packing, physical registers, and their resource bounds are separate
refinements of this arithmetic specification.

The source coordinates are `remainder = r_(i-1)`, `divisor = r_i`,
`coefficient = t_i`, and `previousCoefficient = t_(i-1)`.
The conserved quantity is `r_(i-1)*t_i + r_i*t_(i-1)`
[LYL+26, sec_EEA/sub_regshare.tex:4-12]. The quotient can be recovered from
the updated coefficient pair, so no quotient is silently discarded at an
iteration boundary.

Preprocessing folds inputs above half the modulus and retains the complement
bit [LYL+26, sec_EEA/sub_4phase.tex:112-128]. The local admissibility predicate
is established from the original positive-residue domain by that preprocessing
and preserved by active iterations. It is not a new caller domain restriction.
No terminal padding or erasure of the remaining forward EEA state is defined
here; the source retains that state for reversal.
-/

namespace QuantumAlg.NumberTheory.SharedEEA

/-- Arithmetic data at the boundary between complete four-phase iterations. -/
structure IterationState where
  /-- The preceding Euclidean remainder. -/
  remainder : Nat
  /-- The current divisor; zero denotes the terminal boundary. -/
  divisor : Nat
  /-- The current nonnegative coefficient paired with the preceding remainder. -/
  coefficient : Nat
  /-- The preceding nonnegative coefficient paired with the current divisor. -/
  previousCoefficient : Nat
deriving DecidableEq

namespace IterationState

/-- The source initialization before the first complete iteration. -/
def initial (modulus input : Nat) : IterationState :=
  ⟨modulus, input, 1, 0⟩

/-- The complete quotient that phases two and three compute and consume. -/
def quotient (state : IterationState) : Nat := state.remainder / state.divisor

/-- The conserved positive cross-sum controlling shared storage capacity. -/
def balance (state : IterationState) : Nat :=
  state.remainder * state.coefficient + state.divisor * state.previousCoefficient

/-- One complete Euclidean/coefficient iteration, including the final pair exchange. -/
def step (state : IterationState) : IterationState :=
  ⟨state.divisor, state.remainder % state.divisor,
    state.previousCoefficient + state.coefficient * state.quotient, state.coefficient⟩

/-- Recover the consumed quotient from the updated coefficient pair. -/
def recoveredQuotient (state : IterationState) : Nat :=
  state.coefficient / state.previousCoefficient

/-- Reconstruct the preceding iteration data from the actual updated data. -/
def rewind (state : IterationState) : IterationState :=
  ⟨state.divisor + state.remainder * state.recoveredQuotient, state.remainder,
    state.previousCoefficient, state.coefficient % state.previousCoefficient⟩

/-- Reachable coefficient and remainder ordering at an iteration boundary.
The last condition handles the initial zero coefficient without losing its
quotient-two boundary after the source's input fold. -/
structure Admissible (state : IterationState) : Prop where
  coefficient_pos : 0 < state.coefficient
  previous_lt : state.previousCoefficient < state.coefficient
  divisor_lt : state.divisor < state.remainder
  initial_separation : state.previousCoefficient = 0 → 2 * state.divisor ≤ state.remainder

/-- The initial cross-sum equals the modulus for every input. -/
lemma initial_balance (modulus input : Nat) : (initial modulus input).balance = modulus := by
  simp [initial, balance]

/-- A positive input at most half the modulus gives the required initial ordering. -/
lemma initial_admissible (modulus input : Nat)
    (positive : 0 < input) (halfBound : 2 * input ≤ modulus) :
    (initial modulus input).Admissible := by
  constructor
  · change 0 < 1
    decide
  · change 0 < 1
    decide
  · change input < modulus
    omega
  · intro _
    exact halfBound

/-- The complete iteration preserves the exact cross-sum, including zero remainders. -/
lemma step_balance (state : IterationState) : (step state).balance = state.balance := by
  change state.divisor *
      (state.previousCoefficient + state.coefficient * (state.remainder / state.divisor)) +
      state.remainder % state.divisor * state.coefficient =
    state.remainder * state.coefficient + state.divisor * state.previousCoefficient
  calc
    _ = (state.remainder % state.divisor +
          state.divisor * (state.remainder / state.divisor)) * state.coefficient +
        state.divisor * state.previousCoefficient := by ring
    _ = _ := by rw [Nat.mod_add_div]

/-- The complete iteration has the same remainder GCD as its input. -/
lemma step_gcd (state : IterationState) :
    Nat.gcd (step state).remainder (step state).divisor =
      Nat.gcd state.remainder state.divisor := by
  change Nat.gcd state.divisor (state.remainder % state.divisor) = _
  rw [Nat.gcd_comm state.divisor, ← Nat.gcd_rec, Nat.gcd_comm]

/-- An active iteration strictly decreases the current divisor. -/
lemma step_divisor_lt (state : IterationState) (active : 0 < state.divisor) :
    (step state).divisor < state.divisor :=
  Nat.mod_lt state.remainder active

/-- A proper active remainder pair has a positive Euclidean quotient. -/
lemma quotient_pos (state : IterationState) (ordered : state.divisor < state.remainder)
    (active : 0 < state.divisor) : 0 < state.quotient :=
  Nat.div_pos (Nat.le_of_lt ordered) active

/-- The updated coefficient pair recovers the quotient exactly. -/
lemma recoveredQuotient_step (state : IterationState)
    (positive : 0 < state.coefficient)
    (previousBound : state.previousCoefficient < state.coefficient) :
    (step state).recoveredQuotient = state.quotient := by
  change (state.previousCoefficient + state.coefficient * state.quotient) /
    state.coefficient = state.quotient
  rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt previousBound, Nat.zero_add]

/-- The updated coefficient pair also recovers the previous coefficient exactly. -/
lemma previousCoefficient_step_recovered (state : IterationState)
    (previousBound : state.previousCoefficient < state.coefficient) :
    (step state).coefficient % (step state).previousCoefficient =
      state.previousCoefficient := by
  change (state.previousCoefficient + state.coefficient * state.quotient) %
    state.coefficient = state.previousCoefficient
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt previousBound]

/-- The complete iteration has a real left inverse on its reachable coefficient range.
The updated remainder and coefficient data themselves reconstruct the old data. -/
lemma rewind_step (state : IterationState)
    (positive : 0 < state.coefficient)
    (previousBound : state.previousCoefficient < state.coefficient) :
    rewind (step state) = state := by
  change IterationState.mk
    (state.remainder % state.divisor + state.divisor * (step state).recoveredQuotient)
    state.divisor state.coefficient
    ((step state).coefficient % (step state).previousCoefficient) = state
  rw [recoveredQuotient_step state positive previousBound,
    previousCoefficient_step_recovered state previousBound]
  change IterationState.mk
    (state.remainder % state.divisor + state.divisor * (state.remainder / state.divisor))
    state.divisor state.coefficient state.previousCoefficient = state
  rw [Nat.mod_add_div]

/-- Equality of complete outputs implies equality of admissible iteration inputs. -/
lemma step_injective_on_admissible {left right : IterationState}
    (leftValid : left.Admissible) (rightValid : right.Admissible)
    (same : step left = step right) : left = right := by
  calc
    left = rewind (step left) :=
      (rewind_step left leftValid.coefficient_pos leftValid.previous_lt).symm
    _ = rewind (step right) := congrArg rewind same
    _ = right := rewind_step right rightValid.coefficient_pos rightValid.previous_lt

/-- Active admissible iterations strictly increase the current coefficient.
The zero previous coefficient is handled by the actual quotient-two boundary. -/
lemma coefficient_lt_step (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) : state.coefficient < (step state).coefficient := by
  change state.coefficient < state.previousCoefficient + state.coefficient * state.quotient
  by_cases previousZero : state.previousCoefficient = 0
  · have twoLe : 2 ≤ state.quotient :=
      (Nat.le_div_iff_mul_le active).mpr (valid.initial_separation previousZero)
    have productBound := Nat.mul_le_mul_left state.coefficient twoLe
    have positive := valid.coefficient_pos
    omega
  · have oneLe : 1 ≤ state.quotient := quotient_pos state valid.divisor_lt active
    have productBound := Nat.mul_le_mul_left state.coefficient oneLe
    omega

/-- Every active complete iteration preserves the reachable ordering conditions. -/
lemma step_admissible (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) : (step state).Admissible := by
  have increasing := coefficient_lt_step state valid active
  constructor
  · exact valid.coefficient_pos.trans increasing
  · exact increasing
  · exact step_divisor_lt state active
  · intro zeroPrevious
    change state.coefficient = 0 at zeroPrevious
    exact False.elim (Nat.ne_of_gt valid.coefficient_pos zeroPrevious)

/-- Each shared remainder/coefficient product is bounded by the conserved cross-sum. -/
lemma products_le_balance (state : IterationState) :
    state.remainder * state.coefficient ≤ state.balance ∧
      state.divisor * state.previousCoefficient ≤ state.balance :=
  ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩

/-- The smallest prime input reaches its genuine zero-divisor terminal boundary. -/
lemma step_initial_two_one : step (initial 2 1) = ⟨1, 0, 2, 1⟩ := by decide

end IterationState

/-- Source preprocessing and the explicit bit recording whether complementation occurred. -/
def foldInput (modulus input : Nat) : Bool × Nat :=
  if modulus / 2 < input then (true, modulus - input) else (false, input)

/-- Reconstruct the input using its retained complement bit. -/
def unfoldInput (modulus : Nat) (record : Bool × Nat) : Nat :=
  if record.1 then modulus - record.2 else record.2

/-- The input fold is reversible when its source complement bit is retained. -/
lemma unfoldInput_foldInput (modulus input : Nat) (bounded : input ≤ modulus) :
    unfoldInput modulus (foldInput modulus input) = input := by
  by_cases complemented : modulus / 2 < input
  · simp only [foldInput, if_pos complemented]
    change modulus - (modulus - input) = input
    omega
  · simp [foldInput, unfoldInput, complemented]

/-- Every original positive residue produces a positive folded residue at most half the modulus. -/
lemma foldInput_positive_half (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    0 < (foldInput modulus input).2 ∧ 2 * (foldInput modulus input).2 ≤ modulus := by
  by_cases complemented : modulus / 2 < input
  · simp only [foldInput, complemented, if_true]
    omega
  · simp only [foldInput, complemented, if_false]
    omega

/-- Source preprocessing establishes admissibility on the original positive-residue domain. -/
lemma folded_initial_admissible (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    (IterationState.initial modulus (foldInput modulus input).2).Admissible := by
  obtain ⟨foldedPositive, foldedHalf⟩ := foldInput_positive_half modulus input positive bounded
  exact IterationState.initial_admissible modulus _ foldedPositive foldedHalf

/-- Folding preserves the GCD of the modulus and input. -/
lemma foldInput_gcd (modulus input : Nat) (bounded : input ≤ modulus) :
    Nat.gcd modulus (foldInput modulus input).2 = Nat.gcd modulus input := by
  by_cases complemented : modulus / 2 < input
  · simp only [foldInput, complemented, if_true]
    exact Nat.gcd_self_sub_right bounded
  · simp only [foldInput, complemented, if_false]

/-- The smallest prime does not require an input complement. -/
lemma foldInput_two_one : foldInput 2 1 = (false, 1) := by decide

/-- A residue above half the next prime retains the complemented branch explicitly. -/
lemma foldInput_three_two : foldInput 3 2 = (true, 1) := by decide

end QuantumAlg.NumberTheory.SharedEEA
