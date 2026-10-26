/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare.Encoded
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Narrow
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Wide

/-!
# Complete actual prepared mask equals the original length-read specification

All quantum preparation instructions and controls are already supplied by
the actual native program. Clean initial pool readouts identify its mask
with the original region size for both public width cases. Every finite
other key, empty region and original control value remains admitted.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The actual complete preparation selects the original finite length mask and no surrogate. -/
lemma mask_eq_original (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    LengthCopy.mask width (decide (LengthClip.narrow width))
        (step width field first capacity state) =
      if state.1.control then BitVec.ofNat width.size
        (LengthRead.payloadValue field (boundaryValue field state.1) first state.1).size else 0 :=
  by
  let encoded := encodedState width field first capacity state
  have prefixClean : encoded.2.2.1 = 0 :=
    encoded_prefix width field first capacity state prefixZero
  have conjunctionClean : encoded.2.2.2 = false :=
    (encoded_conjunction width field first capacity state prefixZero).trans borrowZero
  have retainedKey := encoded_boundary width field first capacity state prefixZero
  have retainedControl := encoded_control width field first capacity state prefixZero
  have firstPosition := encoded_address_toNat width field first capacity state prefixZero
    addressZero sentinelFits
  have clipping :
      (if encoded.1.control then
        (LengthBoundary.naturalConstant width field - (boundaryValue field encoded.1).toNat -
          encoded.2.1.toNat) % 2 ^ width.size else 0) =
        if state.1.control then
          (LengthRead.payloadValue field (boundaryValue field state.1) first state.1).size %
            2 ^ width.size else 0 := by
    rw [retainedControl, retainedKey, firstPosition]
    by_cases enabled : state.1.control = true
    · simp only [enabled, if_true]
      congr 1
      rw [← LengthBoundary.region_eq]
      exact (LengthAlignment.clipped_size width field first state).symm
    · simp only [enabled, Bool.false_eq_true, if_false]
  have actualMask :
      (LengthCopy.mask width (decide (LengthClip.narrow width))
        (step width field first capacity state)).toNat =
      if state.1.control then
        (LengthRead.payloadValue field (boundaryValue field state.1) first state.1).size %
          2 ^ width.size else 0 := by
    change (LengthCopy.mask width (decide (LengthClip.narrow width))
      (LengthClip.prepareStep width field encoded)).toNat = _
    by_cases narrowCase : LengthClip.narrow width
    · have encodedFits : encoded.2.1.toNat < 2 ^ width.size := by
        rw [firstPosition]
        by_cases enabled : state.1.control = true
        · rw [if_pos enabled]
          exact (Nat.sub_le (width + 3) _).trans_lt narrowCase
        · rw [if_neg enabled]
          exact Nat.two_pow_pos width.size
      rw [decide_eq_true narrowCase,
        LengthClip.prepareStep_mask_toNat width field encoded narrowCase prefixClean
          conjunctionClean encodedFits]
      exact clipping
    · rw [decide_eq_false narrowCase,
        LengthClip.prepareStep_wide_mask_toNat width field encoded narrowCase prefixClean
          conjunctionClean sentinelFits]
      exact clipping
  apply BitVec.toNat_inj.mp
  rw [actualMask]
  cases state.1.control <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare
