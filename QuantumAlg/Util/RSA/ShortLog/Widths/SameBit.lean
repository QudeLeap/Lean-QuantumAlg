/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths
import all QuantumAlg.Util.RSA.FixedWidthSampling

/-!
# Same-bit coordinate width for the original short-log parameters

The identity specializes the unchanged operand envelope to an arbitrary
same-bit RSA key. It uses only public integer parameters and does not depend
on an execution, stored layout, or resource projection.
-/

namespace QuantumAlg.RSA.ShortLogWidths

/-- The original same-bit parameters have this exact conservative coordinate width. -/
lemma coordinateWidth_sameBit_parameters {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) :
    coordinateWidth pair.modulus (RSA.GeneratorOrder.m n) (RSA.GeneratorOrder.ell n) =
      2 ^ 21 * (3 * n + (n + 2) / 2 + 2) + 2 := by
  unfold coordinateWidth operandWidthBound inputBitWidth RSA.shortLogRecoveryInputBits
  rw [RSA.FixedWidthSampling.modulus_size_eq_two_mul pair positive]
  unfold RSA.GeneratorOrder.m RSA.GeneratorOrder.ell
  norm_num
  ring

end QuantumAlg.RSA.ShortLogWidths
