/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths

/-!
# Exact source capacities of the original short-log recovery width

The original public width contains both source exponent-register indices
and the lattice modulus itself. They also fit strictly below its positive
two's-complement boundary. These are consequences of the unchanged integer
width formula for every public parameter value, without modulus or parity
assumptions.
-/

namespace QuantumAlg.RSA.ShortLogWidths

/-- The source register exponent is strictly below the original arithmetic word width. -/
lemma shortLog_sourceExponent_lt_coordinateWidth (N m ell : Nat) :
    ell + m < coordinateWidth N m ell := by
  have contains := sourceWidth_le_coordinateWidth N m ell
  omega

/-- The actual source lattice modulus fits strictly inside the original unsigned word capacity. -/
lemma shortLog_sourceModulus_lt_coordinateCapacity (N m ell : Nat) :
    2 ^ (ell + m) < 2 ^ coordinateWidth N m ell :=
  Nat.pow_lt_pow_right (by decide) (shortLog_sourceExponent_lt_coordinateWidth N m ell)

/-- The original formula leaves a strict sign-bit margin beyond the complete source register. -/
lemma shortLog_sourceExponent_lt_signExponent (N m ell : Nat) :
    ell + m < coordinateWidth N m ell - 1 := by
  unfold coordinateWidth operandWidthBound inputBitWidth RSA.shortLogRecoveryInputBits
  have twoPow : (2 : Nat) ^ 20 = 1_048_576 := by norm_num
  rw [twoPow]
  omega

/-- Every nonnegative initial basis coordinate lies below the original positive signed capacity. -/
lemma shortLog_sourceModulus_lt_signedCapacity (N m ell : Nat) :
    2 ^ (ell + m) < 2 ^ (coordinateWidth N m ell - 1) :=
  Nat.pow_lt_pow_right (by decide) (shortLog_sourceExponent_lt_signExponent N m ell)

end QuantumAlg.RSA.ShortLogWidths
