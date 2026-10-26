/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import Mathlib.Data.Nat.Size

/-! # Exact word size for the original P-256 modulus, without expanding an EEA program -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion

lemma modulus_nontrivial : 1 < modulus := by
  norm_num [modulus, capacity, complement, width]

lemma modulus_size : modulus.size = 256 := by
  have lower : 2 ^ 255 ≤ modulus := by
    norm_num [modulus, capacity, complement, width]
  have upper : modulus.size ≤ 256 := Nat.size_le.mpr (by
    simpa only [capacity, width] using modulus_lt_capacity)
  have positive : 255 < modulus.size := Nat.lt_size.mpr lower
  omega

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Inversion
