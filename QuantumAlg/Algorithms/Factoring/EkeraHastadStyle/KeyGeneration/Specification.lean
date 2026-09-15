/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
public import QuantumAlg.Util.RSA.KeyGeneration
public import QuantumAlg.Util.RSA.GeneratorOrder

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Util.NumberTheory.Factoring
import all QuantumAlg.Util.RSA.GeneratorOrder
import Mathlib.Tactic.Linarith

/-!
# Canonical Ekerå–Håstad proof-side key model

The executable endpoint receives only the known modulus.  Same-bit factors,
the effective-width premise, and the common-divisor tail condition belong to
this proof-side model and are used only for the conditional pointwise theorem.
The source-faithful key-generation average is stated separately.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical

noncomputable section

/-- Semiprime certificate carried by one theorem-side same-bit RSA key. -/
def semiprimeOfKeyPair {b : Nat} (pair : RSA.RSAKeyPairBits b) :
    NumberTheory.Factoring.SemiprimeFactorModel pair.modulus := by
  unfold RSA.RSAKeyPairBits.modulus
  exact NumberTheory.Factoring.SemiprimeFactorModel.ofDistinctPrimes
    pair.p_prime pair.q_prime pair.p_ne_q

/-- Every theorem-side key gives the same N-only executable assumption; its
factors remain absent from the runtime input. -/
theorem inputOfKeyPair {b : Nat} (pair : RSA.RSAKeyPairBits b) :
    Input pair.modulus where
  modulus_gt_one := by
    unfold RSA.RSAKeyPairBits.modulus
    have left := pair.p_prime.two_le
    have right := pair.q_prime.two_le
    nlinarith

/-- One same-bit RSA key outside the key-level exceptional event. -/
public structure GoodKeyModel (N : Nat) where
  /-- Exact bit width of either generated prime. -/
  bitWidth : Nat
  /-- Ordered pair from the theorem-side same-bit RSA carrier. -/
  pair : RSA.RSAKeyPairBits bitWidth
  /-- The executable modulus is exactly the generated product. -/
  modulus_eq : N = pair.modulus
  /-- Width is inside the effective analytic range. -/
  effective : RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth
  /-- The one-time key-level common-divisor loss does not occur. -/
  keyGood : Nat.gcd (pair.p - 1) (pair.q - 1) <
    2 ^ RSA.GeneratorOrder.gcdLossBits bitWidth

namespace GoodKeyModel

/-- Forget the probability-side key conditions and retain the semiprime
factor certificate used by the output specification. -/
def semiprime {N : Nat} (model : GoodKeyModel N) :
    NumberTheory.Factoring.SemiprimeFactorModel N := by
  rw [model.modulus_eq]
  exact semiprimeOfKeyPair model.pair

/-- The proof-side model supplies the public-modulus executable assumption. -/
public theorem input {N : Nat} (model : GoodKeyModel N) : Input N where
  modulus_gt_one := by
    rw [model.modulus_eq, RSA.RSAKeyPairBits.modulus]
    have left := model.pair.p_prime.two_le
    have right := model.pair.q_prime.two_le
    nlinarith

@[simp] theorem semiprime_leftFactor {N : Nat} (model : GoodKeyModel N) :
    model.semiprime.leftFactor = model.pair.p := by
  rcases model with ⟨_bitWidth, pair, rfl, _effective, _keyGood⟩
  rfl

@[simp] theorem semiprime_rightFactor {N : Nat} (model : GoodKeyModel N) :
    model.semiprime.rightFactor = model.pair.q := by
  rcases model with ⟨_bitWidth, pair, rfl, _effective, _keyGood⟩
  rfl

end GoodKeyModel

end

end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
