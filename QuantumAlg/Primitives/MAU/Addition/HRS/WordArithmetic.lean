/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Bridge
import all QuantumAlg.Util.Classical.Arithmetic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact arithmetic of the HRS recursive constant adder

Carry into the high half is added before the two independent recursive
constant additions [HRS16, paper.tex:232-245]. These finite-word identities
include empty halves and use the already verified fixed-width add/carry
reconstruction theorem. They assert arithmetic, not a circuit implementation.
-/

namespace QuantumAlg.MAU.Addition.HRS

/-- Addition of a compile-time constant on the exact finite-word carrier. -/
def addWord {width : Nat} (constant word : Fin (2 ^ width)) : Fin (2 ^ width) :=
  ⟨(word.val + constant.val) % 2 ^ width, Nat.mod_lt _ (Nat.two_pow_pos width)⟩

/-- A preceding carry increment contributes its Boolean value modulo the high width. -/
theorem hrsAddWord_after_increment_value (width : Nat)
    (constant word : Fin (2 ^ width)) (carry : Bool) :
    (addWord constant (if carry then incrementWord word else word)).val =
      (word.val + constant.val + carry.toNat) % 2 ^ width := by
  cases carry <;>
    simp [addWord, incrementWord, Nat.add_mod, Nat.add_assoc, Nat.add_comm]

private theorem halves_add_mod (low high : Nat)
    (inputLow constantLow : Fin (2 ^ low)) (inputHigh constantHigh : Fin (2 ^ high)) :
    ((inputLow.val + 2 ^ low * inputHigh.val) +
        (constantLow.val + 2 ^ low * constantHigh.val)) % (2 ^ low * 2 ^ high) =
      (inputLow.val + constantLow.val) % 2 ^ low +
        2 ^ low * ((inputHigh.val + constantHigh.val +
          (decide (2 ^ low ≤ inputLow.val + constantLow.val)).toNat) % 2 ^ high) := by
  let carry := (decide (2 ^ low ≤ inputLow.val + constantLow.val)).toNat
  let remainder := (inputLow.val + constantLow.val) % 2 ^ low
  let upper := inputHigh.val + constantHigh.val + carry
  have hlow : remainder + carry * 2 ^ low = inputLow.val + constantLow.val :=
    ClassicalAlgorithms.AddCarry.addCarry_eval_reconstruct
      ⟨inputLow, constantLow⟩
  have hrem : remainder < 2 ^ low := Nat.mod_lt _ (Nat.two_pow_pos low)
  have hupper : upper % 2 ^ high < 2 ^ high := Nat.mod_lt _ (Nat.two_pow_pos high)
  have hbound : remainder + 2 ^ low * (upper % 2 ^ high) < 2 ^ low * 2 ^ high := by
    have hmul := Nat.mul_le_mul_left (2 ^ low) (Nat.succ_le_of_lt hupper)
    nlinarith
  have hsum : (inputLow.val + 2 ^ low * inputHigh.val) +
      (constantLow.val + 2 ^ low * constantHigh.val) = remainder + 2 ^ low * upper := by
    calc
      _ = (inputLow.val + constantLow.val) +
          2 ^ low * (inputHigh.val + constantHigh.val) := by ring
      _ = (remainder + carry * 2 ^ low) +
          2 ^ low * (inputHigh.val + constantHigh.val) := by rw [hlow]
      _ = _ := by dsimp [upper]; ring
  change _ = remainder + 2 ^ low * (upper % 2 ^ high)
  rw [hsum]
  have hquot := Nat.mod_add_div upper (2 ^ high)
  calc
    (remainder + 2 ^ low * upper) % (2 ^ low * 2 ^ high) =
        ((remainder + 2 ^ low * (upper % 2 ^ high)) +
          (2 ^ low * 2 ^ high) * (upper / 2 ^ high)) % (2 ^ low * 2 ^ high) := by
      congr 1
      calc
        remainder + 2 ^ low * upper =
            remainder + 2 ^ low * (upper % 2 ^ high + 2 ^ high * (upper / 2 ^ high)) := by
          rw [hquot]
        _ = _ := by ring
    _ = _ := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbound]

/-- Carry-first high increment followed by separate half additions is full-width addition. -/
theorem hrsAddWord_halves (low high : Nat)
    (inputLow constantLow : Fin (2 ^ low)) (inputHigh constantHigh : Fin (2 ^ high)) :
    addWord (prodEquiv (constantHigh, constantLow)) (prodEquiv (inputHigh, inputLow)) =
      prodEquiv
        (addWord constantHigh
          (if decide (2 ^ low ≤ inputLow.val + constantLow.val)
            then incrementWord inputHigh else inputHigh), addWord constantLow inputLow) := by
  apply Fin.ext
  change ((inputLow.val + 2 ^ low * inputHigh.val) +
      (constantLow.val + 2 ^ low * constantHigh.val)) % 2 ^ (high + low) =
    (addWord constantLow inputLow).val + 2 ^ low *
      (addWord constantHigh (if decide (2 ^ low ≤ inputLow.val + constantLow.val)
        then incrementWord inputHigh else inputHigh)).val
  rw [hrsAddWord_after_increment_value, pow_add, Nat.mul_comm (2 ^ high) (2 ^ low)]
  exact halves_add_mod low high inputLow constantLow inputHigh constantHigh

end QuantumAlg.MAU.Addition.HRS
