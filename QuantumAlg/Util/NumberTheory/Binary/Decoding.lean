/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.NumberTheory.BitComplexity
import Batteries.Data.Nat.Lemmas

/-!
# Exact binary decoding traces

This module turns a fixed-length little-endian bit function into a natural
number while retaining the exact shift-and-add arithmetic executed at every
bit.  The trace is quantum-free and operand-sensitive: neither its value nor
its work list can be supplied independently.
-/

section

namespace QuantumAlg
namespace NumberTheory

/-- One fixed-length `Nat.ofBits` execution and its exact arithmetic. -/
structure NatOfBitsTrace {n : Nat} (bits : Fin n → Bool) where
  private mk ::
  /-- Natural number produced by the recursive shift-and-add execution. -/
  value : Nat
  /-- Reverse accumulator of the operand-derived events. -/
  arithmeticRev : List ArithmeticEvent
  /-- The execution agrees with the canonical little-endian decoder. -/
  canonical : value = Nat.ofBits bits

/-- Exact execution events in chronological order. -/
def NatOfBitsTrace.arithmetic {n : Nat} {bits : Fin n → Bool}
    (trace : NatOfBitsTrace bits) : List ArithmeticEvent :=
  trace.arithmeticRev.reverse

/-- Exact schoolbook charge of one sealed bit-decoding execution. -/
def NatOfBitsTrace.schoolbookCharge {n : Nat} {bits : Fin n → Bool}
    (trace : NatOfBitsTrace bits) : Nat :=
  arithmeticEventListCharge trace.arithmetic

/-- Decode every bit by recursively decoding the higher positions, shifting
that actual result once, and adding the current bit. -/
def natOfBitsTrace : {n : Nat} → (bits : Fin n → Bool) → NatOfBitsTrace bits
  | 0, bits => .mk 0 [] (by simp)
  | n + 1, bits =>
      let tail := natOfBitsTrace (bits ∘ Fin.succ)
      let shifted := tail.value <<< 1
      let digit := (bits 0).toNat
      .mk
        (shifted + digit)
        (.natAdd shifted digit :: .natShiftLeft tail.value 1 ::
          tail.arithmeticRev)
        (by
          rw [Nat.ofBits_succ, ← tail.canonical]
          simp [shifted, digit, Nat.shiftLeft_eq, Nat.mul_comm])

/-- The reverse accumulator has exactly two entries per input bit. -/
private lemma natOfBitsTrace_arithmeticRev_length {n : Nat}
    (bits : Fin n → Bool) :
    (natOfBitsTrace bits).arithmeticRev.length = 2 * n := by
  induction n with
  | zero => simp [natOfBitsTrace]
  | succ n ih =>
      simp only [natOfBitsTrace, List.length_cons]
      rw [ih]
      omega

/-- The exact event list contains one shift and one addition per input bit. -/
lemma natOfBitsTrace_arithmetic_length {n : Nat}
    (bits : Fin n → Bool) :
    (natOfBitsTrace bits).arithmetic.length = 2 * n := by
  simpa [NatOfBitsTrace.arithmetic] using
    natOfBitsTrace_arithmeticRev_length bits

/-- One successor execution appends its shift and addition after all more
significant bits, exactly matching chronological evaluation order. -/
lemma natOfBitsTrace_arithmetic_succ {n : Nat}
    (bits : Fin (n + 1) → Bool) :
    (natOfBitsTrace bits).arithmetic =
      let tail := natOfBitsTrace (bits ∘ Fin.succ)
      let shifted := tail.value <<< 1
      let digit := (bits 0).toNat
      tail.arithmetic ++
        [.natShiftLeft tail.value 1, .natAdd shifted digit] := by
  simp [natOfBitsTrace, NatOfBitsTrace.arithmetic]

/-- The successor charge is exactly the preceding trace charge followed by
the shift and addition performed for the current bit. -/
lemma natOfBitsTrace_schoolbookCharge_succ {n : Nat}
    (bits : Fin (n + 1) → Bool) :
    (natOfBitsTrace bits).schoolbookCharge =
      let tail := natOfBitsTrace (bits ∘ Fin.succ)
      let shifted := tail.value <<< 1
      let digit := (bits 0).toNat
      tail.schoolbookCharge +
        ArithmeticEvent.schoolbookCharge (.natShiftLeft tail.value 1) +
        ArithmeticEvent.schoolbookCharge (.natAdd shifted digit) := by
  rw [NatOfBitsTrace.schoolbookCharge, natOfBitsTrace_arithmetic_succ]
  simp [NatOfBitsTrace.schoolbookCharge, arithmeticEventListCharge,
    Nat.add_assoc]

/-- Every operand used by the recursive decoder fits in the public input bit
width. -/
lemma natOfBitsTrace_maxOperandWidth_le {n : Nat}
    (bits : Fin n → Bool) :
    arithmeticEventListMaxOperandWidth
        (natOfBitsTrace bits).arithmetic ≤ n := by
  induction n with
  | zero =>
      simp [natOfBitsTrace, NatOfBitsTrace.arithmetic,
        arithmeticEventListMaxOperandWidth]
  | succ n ih =>
      let tail := natOfBitsTrace (bits ∘ Fin.succ)
      let shifted := tail.value <<< 1
      let digit := (bits 0).toNat
      have htailLt : tail.value < 2 ^ n := by
        rw [tail.canonical]
        exact Nat.ofBits_lt_two_pow _
      have htailSize : Nat.size tail.value ≤ n := Nat.size_le.2 htailLt
      have hshiftedLt : shifted < 2 ^ (n + 1) := by
        have hmul := (Nat.mul_lt_mul_right (by decide : 0 < 2)).2 htailLt
        simpa [shifted, Nat.shiftLeft_eq, pow_succ] using hmul
      have hshiftedSize : Nat.size shifted ≤ n + 1 :=
        Nat.size_le.2 hshiftedLt
      have hdigitLe : digit ≤ 1 := by
        cases hbit : bits 0 <;> simp [digit, hbit]
      have hdigitSize : Nat.size digit ≤ n + 1 := by
        calc
          Nat.size digit ≤ Nat.size 1 := Nat.size_le_size hdigitLe
          _ = 1 := Nat.size_one
          _ ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hslot :
          arithmeticEventListMaxOperandWidth
              [ .natShiftLeft tail.value 1
              , .natAdd shifted digit ] ≤ n + 1 := by
        apply arithmeticEventListMaxOperandWidth_le
        intro event hevent
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hevent
        rcases hevent with hshift | hadd
        · subst event
          exact max_le (by simp) hshiftedSize
        · subst event
          exact max_le hshiftedSize hdigitSize
      rw [natOfBitsTrace_arithmetic_succ,
        arithmeticEventListMaxOperandWidth_append]
      exact max_le ((ih (bits ∘ Fin.succ)).trans (Nat.le_succ n)) hslot

/-- Exact binary decoding has cubic schoolbook arithmetic charge in the input
length. -/
lemma natOfBitsTrace_schoolbookCharge_cubic {n : Nat}
    (bits : Fin n → Bool) :
    (natOfBitsTrace bits).schoolbookCharge ≤ 8 * (n + 1) ^ 3 := by
  have hwidth := natOfBitsTrace_maxOperandWidth_le bits
  have hpow :
      (arithmeticEventListMaxOperandWidth
          (natOfBitsTrace bits).arithmetic + 1) ^ 2 ≤
        (n + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 1) 2
  have hpoly : 8 * n * (n + 1) ^ 2 ≤ 8 * (n + 1) ^ 3 := by
    calc
      8 * n * (n + 1) ^ 2 = (8 * (n + 1) ^ 2) * n := by ring
      _ ≤ (8 * (n + 1) ^ 2) * (n + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ = 8 * (n + 1) ^ 3 := by ring
  calc
    (natOfBitsTrace bits).schoolbookCharge =
        arithmeticEventListCharge (natOfBitsTrace bits).arithmetic := rfl
    _ ≤ 4 * (natOfBitsTrace bits).arithmetic.length *
          (arithmeticEventListMaxOperandWidth
            (natOfBitsTrace bits).arithmetic + 1) ^ 2 :=
      arithmeticEventListCharge_le _
    _ ≤ 4 * (natOfBitsTrace bits).arithmetic.length * (n + 1) ^ 2 :=
      Nat.mul_le_mul_left (4 * (natOfBitsTrace bits).arithmetic.length) hpow
    _ = 8 * n * (n + 1) ^ 2 := by
      rw [natOfBitsTrace_arithmetic_length]
      ring
    _ ≤ 8 * (n + 1) ^ 3 := hpoly

end NumberTheory
end QuantumAlg

end
