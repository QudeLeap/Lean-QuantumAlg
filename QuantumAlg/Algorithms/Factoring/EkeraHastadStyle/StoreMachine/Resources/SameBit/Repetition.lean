/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.SameBit.Definitions

/-!
# Same-bit specialization of the repeated-member resource bound
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace PublicResourceBounds

noncomputable section

private lemma samplerBound_sameBit {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    ShorStyle.Canonical.Sampler.samplerClassicalBound
        (modulusBits pair.modulus) = 88 * b + 178 := by
  rw [modulusBits_sameBit pair hb]
  unfold ShorStyle.Canonical.Sampler.samplerClassicalBound
    ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel
  ring

private lemma measurementBits_sameBit {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    measurementBits pair.modulus = b + 1 + 2 * tradeoffWidth b := by
  unfold measurementBits tradeoffWidth
  rw [shortLogBits_sameBit pair hb, tradeoffBits_sameBit pair hb]
  unfold RSA.GeneratorOrder.m RSA.GeneratorOrder.ell
  omega

private lemma memberBound_sameBit_le {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    ShortDLP.CompiledMAU.polynomialPrimitiveBound
        (shortLogBits pair.modulus) (tradeoffBits pair.modulus)
        (arithmeticBits pair.modulus) pair.modulus ≤ memberEventBound b := by
  rw [shortLogBits_sameBit pair hb, tradeoffBits_sameBit pair hb,
    arithmeticBits_sameBit pair hb]
  unfold memberEventBound tradeoffWidth RSA.GeneratorOrder.m
    RSA.GeneratorOrder.ell
  exact ShortDLP.CompiledMAU.polynomialPrimitiveBound_le_widthBound
    (b + 1) ((b + 2) / 2) (2 * b) pair.modulus

/-- The generic repetition closed form is bounded by the displayed same-bit
width-only arithmetic formula. -/
lemma retryRepetitionEventCardClosedFormBound_le_sameBit {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    retryRepetitionEventCardClosedFormBound pair.modulus ≤
      repetitionEventBound b := by
  unfold retryRepetitionEventCardClosedFormBound repetitionEventBound
  rw [samplerBound_sameBit pair hb, measurementBits_sameBit pair hb]
  have hmember := memberBound_sameBit_le pair hb
  omega

end

end PublicResourceBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
