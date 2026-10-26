/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.BitVector

/-! # Complete finite natural boundary readout of the actual native preparation -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Public physical region end before subtracting the actual complete other metadata. -/
def naturalConstant (width : Nat) : Field → Nat
  | .coefficient => width + 3
  | .divisor => width + 3 - 1

/-- The exact region end is always inside the original complete word. -/
lemma naturalConstant_le (width : Nat) (field : Field) :
    naturalConstant width field ≤ width + 3 := by
  cases field <;> simp only [naturalConstant] <;> omega

/-- The old full natural region uses this same public end and the actual finite boundary. -/
lemma region_eq (width : Nat) (field : Field) (key : BitVec width.size) :
    region width field key = naturalConstant width field - key.toNat := by
  cases field <;> rfl

/-- The full first-position sentinel fits for widths at least two. Small widths are separate. -/
lemma sentinel_fits (width : Nat) (atLeastTwo : 2 ≤ width) :
    width + 3 < 2 ^ ScanMetadata.addressWidth width := by
  have range := Nat.lt_size_self width
  have lower : 3 ≤ 2 ^ width.size := by omega
  rw [ScanMetadata.addressWidth, Nat.pow_succ]
  omega

/-- The actual loader has the intended natural value when the full physical sentinel fits. -/
lemma constant_toNat (width : Nat) (field : Field)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (constant width field).toNat = naturalConstant width field := by
  have fits := (naturalConstant_le width field).trans_lt sentinelFits
  cases field <;> exact Nat.mod_eq_of_lt fits

/-- Complete paid preparation gives the wrapped original boundary, including oversized keys. -/
lemma prepareStep_toNat (width : Nat) (field : Field) (state : Data width)
    (prefixZero : state.2.2.1 = 0) (conjunctionZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (prepareStep width field state).2.2.1.toNat =
      LengthClip.wrappedDifference (2 ^ ScanMetadata.addressWidth width)
        (naturalConstant width field) (boundaryValue field state.1).toNat := by
  rw [prepareStep_prefix_clean width field state prefixZero conjunctionZero,
    LengthClip.subtraction_toNat, constant_toNat width field sentinelFits,
    BitVec.toNat_cons', Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
