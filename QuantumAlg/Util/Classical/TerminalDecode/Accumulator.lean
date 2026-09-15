/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# Wrapping terminal-bit accumulation from arbitrary initial words

Appending the target width's number of bits multiplies every initial value
by the word modulus. It therefore disappears under the actual wrapping
arithmetic. The remaining result is exactly the fixed-width source decoder;
no initial-zero assumption is needed.
-/

namespace QuantumAlg.ClassicalAlgorithms.TerminalDecode

/-- Reducing the accumulator before one append does not change its final residue. -/
theorem terminalAppend_mod (modulus accumulator : Nat) (bit : Bool) :
    appendBit (accumulator % modulus) bit % modulus =
      appendBit accumulator bit % modulus := by
  simp only [appendBit, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

/-- A wrapping append fold agrees with reducing the corresponding natural fold once. -/
theorem terminalAccumulator_mod (modulus : Nat) (bits : List Bool) (initial : Nat) :
    bits.foldl (fun value bit => appendBit value bit % modulus) (initial % modulus) =
      bits.foldl appendBit initial % modulus := by
  induction bits generalizing initial with
  | nil => rfl
  | cons bit rest ih =>
      simp only [List.foldl_cons, terminalAppend_mod]
      exact ih (appendBit initial bit)

/-- Every source bit doubles the entire previous accumulator contribution. -/
theorem terminalAccumulator_initial_contribution (bits : List Bool) (initial : Nat) :
    bits.foldl appendBit initial =
      initial * 2 ^ bits.length + bits.foldl appendBit 0 := by
  induction bits generalizing initial with
  | nil => simp
  | cons bit rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (appendBit initial bit), ih (appendBit 0 bit)]
      simp only [appendBit, pow_succ]
      ring

/-- The actual list order is the existing pure head-recursive accumulator order. -/
theorem terminalAccumulator_ofFn {width : Nat} (bits : Fin width → Bool) (initial : Nat) :
    (List.ofFn bits).foldl appendBit initial = accumulatorFold width initial bits := by
  induction width generalizing initial with
  | zero => rfl
  | succ width ih =>
      rw [List.ofFn_succ, List.foldl_cons]
      exact ih (bits ∘ Fin.succ) (appendBit initial (bits 0))

/-- Exactly one target-width fold eliminates every initial accumulator residue. -/
theorem terminalAccumulator_width_result {width : Nat}
    (bits : Fin width → Bool) (initial : Nat) :
    (List.ofFn bits).foldl (fun value bit => appendBit value bit % 2 ^ width)
        (initial % 2 ^ width) = Nat.ofBits (bits ∘ Fin.rev) := by
  rw [terminalAccumulator_mod, terminalAccumulator_initial_contribution]
  simp only [List.length_ofFn, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_mod, Nat.zero_add]
  rw [terminalAccumulator_ofFn, accumulatorFold_zero_eq_bigEndianFold,
    bigEndianFold_eq_ofBits, Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)]
  exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow _)

/-- Both source bit orders produce their exact original bounded decode from any accumulator. -/
theorem terminalAccumulator_decodes {width : Nat} (input : Input width) (initial : Nat) :
    (List.ofFn (accumulatorBits input.order input.bits)).foldl
        (fun value bit => appendBit value bit % 2 ^ width) (initial % 2 ^ width) =
      decodeNat input := by
  rw [terminalAccumulator_width_result, decodeNat_eq_bigEndianFold_accumulatorBits,
    bigEndianFold_eq_ofBits]

end QuantumAlg.ClassicalAlgorithms.TerminalDecode
