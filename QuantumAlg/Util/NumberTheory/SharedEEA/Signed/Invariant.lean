/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Iteration
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# Original-input modular invariant and the retained iteration parity

The actual fold replaces a large input by its negative residue and records
that choice in Iter. Every complete macro exchange flips Iter. The two
crossed coefficients consequently retain the original input's signed
modular relation throughout the Euclidean trajectory
[LYL+26, sec_EEA/sub_4phase.tex:113-117,123-125;
LYL+26, sec_EEA/sub_regshare.tex:309-313].

At remainder one and divisor zero, the source's stated sign correction
therefore produces an actual modular inverse. These are arithmetic laws
for the retained physical parity, not a declaration that terminal rotation,
output correction gates, or cleanup of the forward state Gamma is complete.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.SignedInvariant

/-- The actual retained iteration bit chooses the sign of the original-input relation. -/
def sign (modulus : Nat) (iteration : Bool) : ZMod modulus :=
  if iteration then -1 else 1

private lemma sign_flip (modulus : Nat) (iteration : Bool) :
    sign modulus (!iteration) = -sign modulus iteration := by
  cases iteration <;> simp [sign]

/-- Both original-input congruences, with the actual coefficient orientation and retained parity. -/
def Holds (modulus input : Nat) (state : IterationState) (iteration : Bool) : Prop :=
  (state.divisor : ZMod modulus) =
      sign modulus iteration * (input : ZMod modulus) * (state.coefficient : ZMod modulus) ∧
    (state.remainder : ZMod modulus) =
      -sign modulus iteration * (input : ZMod modulus) * (state.previousCoefficient : ZMod modulus)

/-- The real folded value and retained fold bit establish the original-input modular relations. -/
lemma folded_initial (modulus input : Nat) (bounded : input < modulus) :
    Holds modulus input (IterationState.initial modulus (foldInput modulus input).2)
      (foldInput modulus input).1 := by
  by_cases complemented : modulus / 2 < input
  · simp only [foldInput, if_pos complemented]
    constructor
    · simp [IterationState.initial, sign, Nat.cast_sub bounded.le]
    · simp [IterationState.initial, sign]
  · simp only [foldInput, if_neg complemented]
    constructor
    · simp [IterationState.initial, sign]
    · simp [IterationState.initial, sign]

/-- The exact Euclidean/coefficient update preserves both relations under the real Iter flip. -/
lemma step (modulus input : Nat) (state : IterationState) (iteration : Bool)
    (invariant : Holds modulus input state iteration) :
    Holds modulus input (IterationState.step state) (!iteration) := by
  have decomposition := congrArg (fun value : Nat => (value : ZMod modulus))
    (Nat.mod_add_div state.remainder state.divisor)
  simp only [Nat.cast_add, Nat.cast_mul] at decomposition
  have remainder : ((state.remainder % state.divisor : Nat) : ZMod modulus) =
      (state.remainder : ZMod modulus) -
        (state.divisor : ZMod modulus) * (state.quotient : ZMod modulus) :=
    eq_sub_iff_add_eq.mpr decomposition
  constructor
  · change ((state.remainder % state.divisor : Nat) : ZMod modulus) =
      sign modulus (!iteration) * (input : ZMod modulus) *
        ((state.previousCoefficient + state.coefficient * state.quotient : Nat) : ZMod modulus)
    rw [remainder, invariant.1, invariant.2, sign_flip, Nat.cast_add, Nat.cast_mul]
    ring
  · change (state.divisor : ZMod modulus) =
      -sign modulus (!iteration) * (input : ZMod modulus) * (state.coefficient : ZMod modulus)
    rw [sign_flip, neg_neg]
    exact invariant.1

/-- The original source's final conditional correction of the retained coefficient. -/
def output (modulus : Nat) (state : IterationState) (iteration : Bool) : Nat :=
  if iteration then state.previousCoefficient else modulus - state.previousCoefficient

/-- At the true terminal gcd-one boundary, the retained source correction is an actual inverse. -/
lemma terminal_product (modulus input : Nat) (state : IterationState) (iteration : Bool)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (invariant : Holds modulus input state iteration)
    (finished : state.divisor = 0) (unit : state.remainder = 1) :
    (input : ZMod modulus) * (output modulus state iteration : ZMod modulus) = 1 := by
  have coefficient : state.coefficient = modulus := by
    change state.remainder * state.coefficient + state.divisor * state.previousCoefficient =
      modulus at conserved
    simpa only [finished, unit, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using conserved
  have previousBound : state.previousCoefficient ≤ modulus :=
    valid.previous_lt.le.trans coefficient.le
  have relation : (1 : ZMod modulus) =
      -sign modulus iteration * (input : ZMod modulus) *
        (state.previousCoefficient : ZMod modulus) := by
    simpa only [unit, Nat.cast_one] using invariant.2
  cases iteration with
  | false =>
      change (input : ZMod modulus) *
        ((modulus - state.previousCoefficient : Nat) : ZMod modulus) = 1
      rw [Nat.cast_sub previousBound, ZMod.natCast_self]
      calc
        _ = -sign modulus false * (input : ZMod modulus) *
            (state.previousCoefficient : ZMod modulus) := by
          simp only [sign, Bool.false_eq_true, if_false]
          ring
        _ = 1 := relation.symm
  | true =>
      change (input : ZMod modulus) * (state.previousCoefficient : ZMod modulus) = 1
      simpa only [sign, if_true, neg_neg, one_mul] using relation.symm

end QuantumAlg.NumberTheory.SharedEEA.SignedInvariant
