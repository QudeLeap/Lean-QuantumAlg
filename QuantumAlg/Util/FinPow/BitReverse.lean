/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Binary label splitting and reversal

Leading-bit splitting and significant-bit reversal are finite arithmetic
operations. Their original identities require no quantum execution model.
-/

namespace QuantumAlg

noncomputable section

/-- Reverse the `n` significant bits of a computational-basis label. -/
def qftReverseBits (n : Nat) (label : Fin (2 ^ n)) : Fin (2 ^ n) :=
  ⟨Nat.ofBits (fun bit : Fin n => label.val.testBit (Fin.rev bit).val),
    Nat.ofBits_lt_two_pow _⟩

@[simp]
theorem qftReverseBits_testBit (n : Nat) (label : Fin (2 ^ n))
    (bit : Fin n) :
    (qftReverseBits n label).val.testBit bit.val =
      label.val.testBit (Fin.rev bit).val := by
  unfold qftReverseBits
  rw [Nat.testBit_ofBits_lt]

@[simp]
theorem qftReverseBits_involutive (n : Nat) (label : Fin (2 ^ n)) :
    qftReverseBits n (qftReverseBits n label) = label := by
  apply Fin.val_injective
  change Nat.ofBits
      (fun bit : Fin n =>
        (qftReverseBits n label).val.testBit (Fin.rev bit).val) = label.val
  have hfun :
      (fun bit : Fin n =>
        (qftReverseBits n label).val.testBit (Fin.rev bit).val) =
        fun bit : Fin n => label.val.testBit bit.val := by
    funext bit
    rw [qftReverseBits_testBit]
    simp
  rw [hfun, Nat.ofBits_testBit, Nat.mod_eq_of_lt label.isLt]

/-- Bit reversal as a self-inverse basis-label permutation. -/
def qftReverseBitsPerm (n : Nat) : Equiv.Perm (Fin (2 ^ n)) where
  toFun := qftReverseBits n
  invFun := qftReverseBits n
  left_inv := qftReverseBits_involutive n
  right_inv := qftReverseBits_involutive n

/-- Big-endian splitting of an `(n+1)`-qubit basis label into its leading bit
and lower `n`-bit tail. -/
def qftPairEquiv (n : Nat) :
    Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  (prodEquiv (m := 1) (n := n)).trans
    (finCongr (by rw [Nat.add_comm 1 n]))

@[simp]
theorem qftPairEquiv_apply_val (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val = tail.val + 2 ^ n * head.val :=
  rfl

theorem qftPairEquiv_testBit_high (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val.testBit n = decide (head = 1) := by
  rw [qftPairEquiv_apply_val]
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add head.val tail.isLt n]
  fin_cases head
  · simp
  · simp

theorem qftPairEquiv_mod_tail (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftPairEquiv n (head, tail)).val % 2 ^ n = tail.val := by
  rw [qftPairEquiv_apply_val, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt tail.isLt

theorem qftPairEquiv_testBit_low (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) (bit : Fin n) :
    (qftPairEquiv n (head, tail)).val.testBit bit.val =
      tail.val.testBit bit.val := by
  rw [qftPairEquiv_apply_val, Nat.add_comm,
    Nat.testBit_two_pow_mul_add head.val tail.isLt bit.val]
  simp [bit.isLt]

/-- Bit reversal moves the leading bit to the least-significant position and
recursively reverses the lower label. -/
theorem qftReverseBits_pair (n : Nat) (head : Fin 2)
    (tail : Fin (2 ^ n)) :
    (qftReverseBits (n + 1) (qftPairEquiv n (head, tail))).val =
      2 * (qftReverseBits n tail).val + head.val := by
  change Nat.ofBits (fun bit : Fin (n + 1) =>
      (qftPairEquiv n (head, tail)).val.testBit (Fin.rev bit).val) = _
  rw [Nat.ofBits_succ]
  congr 1
  · congr 1
    apply congrArg Nat.ofBits
    funext bit
    have hlow := qftPairEquiv_testBit_low n head tail (Fin.rev bit)
    simpa [Fin.rev] using hlow
  · have hhigh := qftPairEquiv_testBit_high n head tail
    fin_cases head <;> simpa [Fin.rev] using congrArg Bool.toNat hhigh

end

end QuantumAlg
