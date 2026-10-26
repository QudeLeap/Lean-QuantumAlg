/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Bool.Basic

/-!
# Arithmetic of two controlled offsets and a clean reduction flag

This reduction is a project derivation using the constant-addition primitive
[G25, main.tex:199-295,354-360]. The first comparison chooses the non-wrapping
addition. Toggling the flag
then chooses the complementary offset on the wrapping branch. The final
comparison clears that same flag. These are finite-word arithmetic facts;
the native comparison and measured-adder implementations must establish their
own state and resource obligations.
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction

/-- The independently specified controlled modular addition. -/
def output (modulus constant input : Nat) (active : Bool) : Nat :=
  if active then (input + constant) % modulus else input

/-- The first comparison chooses precisely the branch whose ordinary sum is below the modulus. -/
def firstFlag (modulus constant input : Nat) (active : Bool) : Bool :=
  active && decide (input < modulus - constant)

/-- The first actual width-limited offset. -/
def firstWord (capacity modulus constant input : Nat) (active : Bool) : Nat :=
  if firstFlag modulus constant input active then (input + constant) % capacity else input

/-- Toggling by the active control selects the complementary second offset. -/
def secondFlag (modulus constant input : Nat) (active : Bool) : Bool :=
  firstFlag modulus constant input active ^^ active

/-- The second actual width-limited offset uses the static complementary constant. -/
def secondWord (capacity modulus constant input : Nat) (active : Bool) : Nat :=
  let intermediate := firstWord capacity modulus constant input active
  if secondFlag modulus constant input active then
    (intermediate + (capacity + constant - modulus)) % capacity
  else intermediate

/-- Two actual width-limited additions give the independent controlled modular result. -/
lemma secondWord_eq_output {capacity modulus constant input : Nat}
    (modulusFits : modulus ≤ capacity)
    (constantBound : constant < modulus) (inputBound : input < modulus) (active : Bool) :
    secondWord capacity modulus constant input active = output modulus constant input active := by
  cases active with
  | false => rfl
  | true =>
      by_cases small : input < modulus - constant
      · have sumBound : input + constant < modulus := by omega
        simp [secondWord, secondFlag, firstWord, firstFlag, output, small,
          Nat.mod_eq_of_lt sumBound, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le sumBound modulusFits)]
      · have wraps : modulus ≤ input + constant := by omega
        have reducedBound : input + constant - modulus < modulus := by omega
        have packed : input + (capacity + constant - modulus) =
            capacity + (input + constant - modulus) := by omega
        have expanded : input + constant = modulus + (input + constant - modulus) := by omega
        have remainder : (input + constant) % modulus = input + constant - modulus := by
          calc
            _ = (modulus + (input + constant - modulus)) % modulus :=
              congrArg (fun value => value % modulus) expanded
            _ = _ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt reducedBound]
        simp only [secondWord, secondFlag, firstWord, firstFlag, output, Bool.true_and,
          decide_eq_false small, Bool.false_xor, Bool.false_eq_true, if_false, if_true]
        rw [packed, Nat.add_mod_left,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le reducedBound modulusFits), remainder]

/-- The final comparison removes the reduction flag, including a zero static offset. -/
lemma finalFlag_eq_false {capacity modulus constant input : Nat}
    (modulusFits : modulus ≤ capacity)
    (constantBound : constant < modulus) (inputBound : input < modulus) (active : Bool) :
    (secondFlag modulus constant input active ^^
      (active && decide
        (secondWord capacity modulus constant input active < constant))) = false := by
  rw [secondWord_eq_output modulusFits constantBound inputBound]
  cases active with
  | false => rfl
  | true =>
      by_cases small : input < modulus - constant
      · have sumBound : input + constant < modulus := by omega
        have notSmall : ¬ input + constant < constant := by omega
        simp [secondFlag, firstFlag, output, small, Nat.mod_eq_of_lt sumBound, notSmall]
      · have wraps : modulus ≤ input + constant := by omega
        have reducedBound : input + constant - modulus < constant := by omega
        have reducedModulus : input + constant - modulus < modulus := by omega
        have expanded : input + constant = modulus + (input + constant - modulus) := by omega
        have remainder : (input + constant) % modulus = input + constant - modulus := by
          calc
            _ = (modulus + (input + constant - modulus)) % modulus :=
              congrArg (fun value => value % modulus) expanded
            _ = _ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt reducedModulus]
        simp [secondFlag, firstFlag, output, small, remainder, reducedBound]

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction
