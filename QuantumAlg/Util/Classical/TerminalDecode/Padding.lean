/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Classical.TerminalDecode

/-!
# Exact leading-zero extension of a finite terminal word

Prefixing an actual false source bit preserves the natural value of a
big-endian terminal word while increasing its declared width by one.
-/

namespace QuantumAlg.ClassicalAlgorithms.TerminalDecode

/-- A leading false bit does not change the exact big-endian natural value. -/
theorem terminalDecode_bigEndian_zero_prefix {width : Nat} (bits : Fin width → Bool) :
    bigEndianFold (Fin.cons false bits) = bigEndianFold bits := by
  rw [← accumulatorFold_zero_eq_bigEndianFold, ← accumulatorFold_zero_eq_bigEndianFold]
  change accumulatorFold width (appendBit 0 false) ((Fin.cons false bits) ∘ Fin.succ) =
    accumulatorFold width 0 bits
  rfl

/-- The widened canonical terminal word represents precisely its original bounded index. -/
theorem terminalDecode_fullRegister_zero_prefix {width : Nat} (bits : Fin width → Bool) :
    (fullRegisterIndex (Fin.cons false bits)).val = (fullRegisterIndex bits).val := by
  rw [fullRegisterIndex_val, fullRegisterIndex_val,
    ← bigEndianFold_eq_ofBits, ← bigEndianFold_eq_ofBits]
  exact terminalDecode_bigEndian_zero_prefix bits

end QuantumAlg.ClassicalAlgorithms.TerminalDecode
