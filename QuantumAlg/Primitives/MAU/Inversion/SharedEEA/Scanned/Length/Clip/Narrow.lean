/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Low
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Natural
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.High
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Mask

/-!
# Exact native narrow clipping with arbitrary original boundary metadata

The actual high address is clean because the encoded first position fits
the low word. Public loading, real validity activation, unconditional low
subtraction, real borrow and native copy controls produce exactly the
original naturally clipped length, including empty and invalid regions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The real narrow preparation's selected mask is the complete natural clipped difference. -/
lemma prepareStep_mask_toNat (width : Nat) (field : Field) (state : Data width)
    (narrowCase : narrow width) (prefixZero : state.2.2.1 = 0)
    (borrowZero : state.2.2.2 = false) (addressFits : state.2.1.toNat < 2 ^ width.size) :
    (LengthCopy.mask width true (prepareStep width field state)).toNat =
      if state.1.control then
        (LengthBoundary.naturalConstant width field - (boundaryValue field state.1).toNat -
          state.2.1.toNat) % 2 ^ width.size else 0 := by
  let loaded := LengthBoundary.prepareStep width field state
  let activated := GateSpec.stepList (activeGates width) loaded
  let fits : width.size ≤ ScanMetadata.addressWidth width := by
    unfold ScanMetadata.addressWidth
    omega
  let done := LengthDifference.step width width.size fits activated
  have actual : prepareStep width field state = done := by
    (simp only [prepareStep, activationStep, activationGates, subtractionWidth,
      if_pos narrowCase]; rfl)
  have positive := Nat.two_pow_pos width.size
  have narrowBound : width + 3 < 2 ^ width.size := narrowCase
  have sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width := by
    rw [ScanMetadata.addressWidth, Nat.pow_succ]
    omega
  have loadedValue : loaded.2.2.1.toNat = wrappedDifference (2 * 2 ^ width.size)
      (LengthBoundary.naturalConstant width field) (boundaryValue field state.1).toNat := by
    simpa only [ScanMetadata.addressWidth, Nat.pow_succ, Nat.mul_comm] using
      LengthBoundary.prepareStep_toNat width field state prefixZero borrowZero sentinelFits
  have loadedAddress : loaded.2.1 = state.2.1 :=
    LengthBoundary.prepareStep_address width field state
  have loadedControl : loaded.1.control = state.1.control :=
    LengthBoundary.prepareStep_original width field state (SharedEEA.controlBit width)
  have loadedBorrow : loaded.2.2.2 = false :=
    (LengthBoundary.prepareStep_conjunction width field state).trans borrowZero
  have activeClean : (LengthCopy.active width true).get loaded = false :=
    active_zero_of_lt width loaded (by rw [loadedAddress]; exact addressFits)
  have activeRead : (LengthCopy.active width true).get done =
      (state.1.control && !(decide (2 ^ width.size ≤ loaded.2.2.1.toNat))) := by
    rw [LengthDifference.step_active width width.size fits
      (by unfold ScanMetadata.addressWidth; omega), activeGates_get_clean width loaded activeClean,
      loadedControl]
  have prefixRead : (LengthDifference.value width width.size true activated).toNat =
      loaded.2.2.1.toNat % 2 ^ width.size := by
    rw [activeGates_low_prefix]
    exact low_toNat loaded.2.2.1 width.size
  have addressRead : (LengthDifference.value width width.size false activated).toNat =
      state.2.1.toNat := by
    rw [activeGates_low_address]
    change (loaded.2.1.extractLsb' 0 width.size).toNat = _
    rw [low_toNat, loadedAddress, Nat.mod_eq_of_lt addressFits]
  have activatedBorrow : activated.2.2.2 = false :=
    (activeGates_conjunction width loaded).trans loadedBorrow
  have borrowRead : done.2.2.2 =
      decide (loaded.2.2.1.toNat % 2 ^ width.size < state.2.1.toNat) := by
    rw [LengthDifference.step_borrow, activatedBorrow, Bool.false_xor, prefixRead, addressRead]
  have valueRead : (LengthCopy.value width done).toNat =
      wrappedDifference (2 ^ width.size) (loaded.2.2.1.toNat % 2 ^ width.size)
        state.2.1.toNat := by
    change (LengthDifference.value width width.size true done).toNat = _
    rw [LengthDifference.step_value, subtraction_toNat, prefixRead, addressRead]
  rw [actual]
  have maskRead : (LengthCopy.mask width true done).toNat =
      if (state.1.control && !(decide (2 ^ width.size ≤ loaded.2.2.1.toNat))) &&
          !(decide (loaded.2.2.1.toNat % 2 ^ width.size < state.2.1.toNat)) then
        wrappedDifference (2 ^ width.size) (loaded.2.2.1.toNat % 2 ^ width.size)
          state.2.1.toNat else 0 := by
    unfold LengthCopy.mask
    change (if (LengthCopy.active width true).get done && !done.2.2.2 then
      LengthCopy.value width done else 0).toNat = _
    rw [activeRead, borrowRead]
    split
    · exact valueRead
    · rfl
  rw [maskRead, loadedValue]
  have boundaryFits : LengthBoundary.naturalConstant width field < 2 ^ width.size :=
    (LengthBoundary.naturalConstant_le width field).trans_lt narrowBound
  have clipped := narrow_copy (2 ^ width.size) (LengthBoundary.naturalConstant width field)
    (boundaryValue field state.1).toNat state.2.1.toNat state.1.control positive boundaryFits
    (boundaryValue field state.1).isLt
  have reduced (capacity left right : Nat) :
      wrappedDifference capacity left right % capacity =
        wrappedDifference capacity left right := Nat.mod_mod _ _
  rw [reduced] at clipped
  exact clipped

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
