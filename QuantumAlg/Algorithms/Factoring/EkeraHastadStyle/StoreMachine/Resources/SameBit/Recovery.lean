/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths

import QuantumAlg.Init
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.Scalar
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Resources.SameBit.Definitions

/-!
# Same-bit identities for individual recovery parameters

These identities do not identify the historical total recovery formula with
the current reusable recovery event ledger.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace PublicResourceBounds

noncomputable section

lemma coordinateWidth_sameBit {b : Nat} (pair : RSA.RSAKeyPairBits b)
    (hb : 1 ≤ b) :
    RSA.ShortLogWidths.coordinateWidth pair.modulus
        (shortLogBits pair.modulus) (tradeoffBits pair.modulus) =
      coordinateWidth b := by
  unfold RSA.ShortLogWidths.coordinateWidth RSA.ShortLogWidths.operandWidthBound
    RSA.ShortLogWidths.inputBitWidth RSA.shortLogRecoveryInputBits coordinateWidth
    tradeoffWidth
  rw [RSA.FixedWidthSampling.modulus_size_eq_two_mul pair hb,
    shortLogBits_sameBit pair hb, tradeoffBits_sameBit pair hb]
  unfold RSA.GeneratorOrder.m RSA.GeneratorOrder.ell
  norm_num
  ring

private lemma nearestPlane_sameBit {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    LatticeRecoveryResources.nearestPlaneSavedTargetCardBound
        (shortLogBits pair.modulus) (tradeoffBits pair.modulus) =
      nearestPlaneEventBound b := by
  rw [shortLogBits_sameBit pair hb, tradeoffBits_sameBit pair hb]
  unfold LatticeRecoveryResources.nearestPlaneSavedTargetCardBound
    RSA.shortLogRecoveryFuel nearestPlaneEventBound tradeoffWidth
    RSA.GeneratorOrder.m RSA.GeneratorOrder.ell
  ring

private lemma quadratic_sameBit {b : Nat}
    (pair : RSA.RSAKeyPairBits b) (hb : 1 ≤ b) :
    LatticeRecoveryResources.quadraticGuardedCardBound
        (RSA.ShortLogWidths.coordinateWidth pair.modulus
          (shortLogBits pair.modulus) (tradeoffBits pair.modulus)) =
      quadraticEventBound b := by
  rw [coordinateWidth_sameBit pair hb]
  unfold LatticeRecoveryResources.quadraticGuardedCardBound
    LatticeRecoveryResources.natSqrtCardBound
    QuadraticPrefix.discriminantWidth QuadraticPrefix.centerWidth
    quadraticEventBound coordinateWidth
  omega

end

end PublicResourceBounds
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
