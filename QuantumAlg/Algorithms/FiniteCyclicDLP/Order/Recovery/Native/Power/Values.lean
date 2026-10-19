/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Power
public import QuantumAlg.Util.Classical.TerminalDecode
public import QuantumAlg.Util.Classical.TerminalDecode.Accumulator
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.TerminalDecode.Accumulator

/-!
# Values computed by the representation-independent group-power scan

The executable scan consumes the complete unsigned word in its stored
most-significant-first order.  Its square-and-multiply recurrence therefore
ends at the natural value represented by that word, without a range or
leading-bit premise.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- One square-and-multiply digit advances the accumulated exponent. -/
public lemma square_multiply_pow (generator : G) (exponent : Nat) (bit : Bool) :
    (generator ^ exponent) ^ 2 *
        (if bit then generator else 1) =
      generator ^ (2 * exponent + bit.toNat) := by
  cases bit
  · simp only [Bool.false_eq_true, if_false, mul_one, Bool.toNat_false, add_zero]
    calc
      (generator ^ exponent) ^ 2 = generator ^ (exponent * 2) :=
        (pow_mul generator exponent 2).symm
      _ = generator ^ (2 * exponent) := by rw [Nat.mul_comm]
  · simp only [if_true, Bool.toNat_true]
    calc
      (generator ^ exponent) ^ 2 * generator =
          generator ^ (exponent * 2) * generator ^ 1 := by
            rw [pow_mul, pow_one]
      _ = generator ^ (exponent * 2 + 1) := (pow_add generator _ _).symm
      _ = generator ^ (2 * exponent + 1) := by rw [Nat.mul_comm]

/-- The complete Core word accessor reconstructs the stored unsigned value
under the accumulator recurrence used by the actual scan. -/
public lemma word_accumulatorFold_eq_toNat {width : Nat}
    (word : CShape.Value (.unsignedWord width)) :
    ClassicalAlgorithms.TerminalDecode.accumulatorFold width 0
        (fun index => (word.wordBitGet index).toBool) = word.toNat := by
  cases word with
  | unsignedWord value =>
      rw [ClassicalAlgorithms.TerminalDecode.accumulatorFold_zero_eq_bigEndianFold,
        ClassicalAlgorithms.TerminalDecode.bigEndianFold_eq_ofBits]
      have bits :
          (fun index : Fin width =>
            ((CShape.Value.unsignedWord value).wordBitGet index).toBool) ∘ Fin.rev =
            fun index : Fin width => value.val.testBit index.val := by
        funext index
        change value.val.testBit (width - 1 - (Fin.rev index).val) =
          value.val.testBit index.val
        congr 1
        rw [Fin.val_rev]
        omega
      rw [bits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]
      rfl

end

end QuantumAlg.FiniteCyclicDLP.OrderRecovery.Native
