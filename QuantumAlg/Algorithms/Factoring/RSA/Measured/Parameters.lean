/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
import all QuantumAlg.Util.RSA.KeyGeneration
import Mathlib.Data.BitVec

/-!
# Original public RSA parameters in the measured arithmetic word

The known modulus alone determines the finite word and all static unit
coefficients. The original total nontrivial-modulus input supplies only the
construction width. Every original ordered key, including an exceptional
key, supplies oddness and the resource width internally [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured

noncomputable section

open EkeraHastadStyle.Canonical

/-- The original public arithmetic width contains exactly the original public modulus. -/
def modulusWord (N : Nat) : BitVec (arithmeticBits N) :=
  BitVec.ofNat (arithmeticBits N) N

/-- Finite-word construction truncates no original public modulus. -/
lemma measuredRSA_modulusWord_toNat (N : Nat) : (modulusWord N).toNat = N := by
  simp only [modulusWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (modulus_lt_arithmeticCapacity N)]

/-- Every original nontrivial-modulus input supplies the measured constructor's width. -/
lemma measuredRSA_arithmeticBits_atLeastTwo {N : Nat} (input : Input N) :
    2 ≤ arithmeticBits N := by
  have capacity := modulus_lt_arithmeticCapacity N
  by_contra small
  have bounded : arithmeticBits N ≤ 1 := by omega
  have powBound : 2 ^ arithmeticBits N ≤ 2 ^ 1 :=
    Nat.pow_le_pow_right (by norm_num) bounded
  norm_num at powBound
  have nontrivial := input.modulus_gt_one
  omega

/-- Static unit coefficients use the same modulus through its proved exact finite word. -/
def unitInWord (N : Nat) (unit : (ZMod N)ˣ) : (ZMod (modulusWord N).toNat)ˣ :=
  cast (congrArg (fun value : Nat => (ZMod value)ˣ) (measuredRSA_modulusWord_toNat N).symm) unit

/-- The complete stored parameter selects the unchanged original source generator. -/
def parameterGenerator (N : Nat) (parameter : (ParameterShape N).Value) :
    (ZMod (modulusWord N).toNat)ˣ :=
  unitInWord N (parameterUnit parameter)

/-- The original source target is transported through the same exact public modulus equality. -/
def parameterTargetWord (N : Nat) (parameter : (ParameterShape N).Value) :
    (ZMod (modulusWord N).toNat)ˣ :=
  unitInWord N (parameterTarget parameter)

/-- Every original ordered prime pair already carries the required odd modulus. -/
lemma measuredRSA_orderedKey_odd {bits : Nat} (pair : QuantumAlg.RSA.RSAKeyPairBits bits) :
    Odd pair.modulus :=
  pair.p_odd.mul pair.q_odd

/-- Distinct odd primes cannot fit an original prime interval of width below three. -/
lemma measuredRSA_orderedKey_primeWidth {bits : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bits) : 3 ≤ bits := by
  have leftBound := pair.p_bits.2
  have rightBound := pair.q_bits.2
  have leftPrime := pair.p_prime.two_le
  have rightPrime := pair.q_prime.two_le
  obtain ⟨leftHalf, leftOdd⟩ := pair.p_odd
  obtain ⟨rightHalf, rightOdd⟩ := pair.q_odd
  have different := pair.p_ne_q
  by_contra small
  have powBound : 2 ^ bits ≤ 4 := by
    calc
      2 ^ bits ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have leftSmall := lt_of_lt_of_le leftBound powBound
  have rightSmall := lt_of_lt_of_le rightBound powBound
  omega

/-- All original ordered keys satisfy the large-width arithmetic envelope without a good-key cut. -/
lemma measuredRSA_orderedKey_arithmeticWidth {bits : Nat}
    (pair : QuantumAlg.RSA.RSAKeyPairBits bits) : 5 ≤ arithmeticBits pair.modulus := by
  rw [arithmeticBits_sameBit pair (by have width := measuredRSA_orderedKey_primeWidth pair; omega)]
  have width := measuredRSA_orderedKey_primeWidth pair
  omega

/-- An original odd public modulus gives the actual word's odd low bit. -/
lemma measuredRSA_modulusWord_lowBit {N : Nat} (odd : Odd N) :
    (modulusWord N).getLsbD 0 = true := by
  change (modulusWord N).toNat.testBit 0 = true
  rw [measuredRSA_modulusWord_toNat]
  simp [Nat.testBit_zero, Nat.odd_iff.mp odd]

end

end QuantumAlg.Factoring.RSA.Measured
