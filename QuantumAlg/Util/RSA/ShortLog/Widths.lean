/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Reduction

/-!
# Original fixed-width bounds for short-log lattice recovery

These are the same input-bit and conservative operand envelopes used by the
source recovery. The doubled operand width and two final bits provide the
original product and sign slack. The definitions depend only on the public
integer parameters; they do not depend on any circuit, stored layout, or
execution-resource projection.
-/

namespace QuantumAlg.RSA.ShortLogWidths

/-- Public input-bit envelope of one two-sample short-log recovery. -/
def inputBitWidth (N m ell : Nat) : Nat :=
  RSA.shortLogRecoveryInputBits N m ell

/-- Conservative operand-width envelope for every canonical candidate slot. -/
def operandWidthBound (N m ell : Nat) : Nat :=
  2 ^ 20 * inputBitWidth N m ell

/-- Uniform two's-complement ALU width.  Doubling the operand envelope leaves
room for a full product, while the final two bits provide sign and strict-bound
slack for exact decoding. -/
def coordinateWidth (N m ell : Nat) : Nat :=
  2 * operandWidthBound N m ell + 2

/-- The uniform coordinate width is positive. -/
lemma coordinateWidth_pos (N m ell : Nat) : 0 < coordinateWidth N m ell := by
  simp [coordinateWidth]

/-- The canonical reduction word contains the complete source target word. -/
lemma sourceWidth_le_coordinateWidth (N m ell : Nat) :
    ell + m + 1 ≤ coordinateWidth N m ell := by
  unfold coordinateWidth operandWidthBound
    inputBitWidth RSA.shortLogRecoveryInputBits
  have twoPow : 2 ^ 20 = 1_048_576 := by norm_num
  rw [twoPow]
  omega

end QuantumAlg.RSA.ShortLogWidths
