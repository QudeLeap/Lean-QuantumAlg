/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Util.FinPow

/-!
# Fixed zero in big-endian binary coordinates

The all-zero physical word and the integer label zero denote the same basis
vector, including the empty word.
-/

namespace QuantumAlg.BinaryBasis

/-- Decoding the zero label yields zero at every actual coordinate. -/
theorem bigEndianEquiv_symm_zero (width : Nat) :
    (bigEndianEquiv width).symm (0 : Fin (2 ^ width)) = (fun _ : Fin width => (0 : Fin 2)) := by
  funext index
  rw [bigEndianEquiv_symm_value]
  change finTwoEquiv.symm (Nat.testBit 0 index.rev.val) = 0
  simp [finTwoEquiv]

/-- Encoding the all-zero word yields the original integer label zero. -/
theorem bigEndianEquiv_zero (width : Nat) :
    bigEndianEquiv width (fun _ : Fin width => (0 : Fin 2)) = (0 : Fin (2 ^ width)) := by
  rw [← bigEndianEquiv_symm_zero, Equiv.apply_symm_apply]

end QuantumAlg.BinaryBasis
