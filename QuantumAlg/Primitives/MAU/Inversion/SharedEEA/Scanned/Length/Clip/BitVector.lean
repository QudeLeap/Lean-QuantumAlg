/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Arithmetic

/-! # Exact fixed-width readout identities for the actual clipping operands -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

/-- Fixed-width subtraction and the independent natural representative agree on all labels. -/
lemma subtraction_toNat {size : Nat} (left right : BitVec size) :
    (left - right).toNat = wrappedDifference (2 ^ size) left.toNat right.toNat := by
  rw [BitVec.toNat_sub, wrappedDifference]
  congr 1
  have fits := right.isLt
  omega

/-- The selected low operand retains exactly the natural value modulo its real capacity. -/
lemma low_toNat {size : Nat} (word : BitVec size) (length : Nat) :
    (word.extractLsb' 0 length).toNat = word.toNat % 2 ^ length := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- The genuine high bit of a one-bit-extended word is the full-capacity validity test. -/
lemma high_get {size : Nat} (word : BitVec (size + 1)) :
    word.getMsbD 0 = decide (2 ^ size ≤ word.toNat) := by
  rw [← BitVec.msb_eq_getMsbD_zero, BitVec.msb_eq_decide]
  rfl

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
