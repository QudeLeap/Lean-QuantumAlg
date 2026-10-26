/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Clip.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Natural
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Mask

/-!
# Exact complete-width clipping near the metadata power boundary

Every finite other key is valid in the public wide case. The actual full
address and prefix participate in the subtraction; the arbitrary original
Ctrl remains its active selector. No nonexistent spare high bit is used.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Full carry subtraction and actual borrow produce the original finite clipped mask. -/
lemma prepareStep_wide_mask_toNat (width : Nat) (field : Field) (state : Data width)
    (wideCase : ¬narrow width) (prefixZero : state.2.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (LengthCopy.mask width false (prepareStep width field state)).toNat =
      if state.1.control then
        (LengthBoundary.naturalConstant width field - (boundaryValue field state.1).toNat -
          state.2.1.toNat) % 2 ^ width.size else 0 := by
  let length := ScanMetadata.addressWidth width
  let loaded := LengthBoundary.prepareStep width field state
  let done := LengthDifference.step width length le_rfl loaded
  have actual : prepareStep width field state = done := by
    (simp only [prepareStep, activationStep, activationGates, subtractionWidth,
      if_neg wideCase, GateSpec.stepList]; rfl)
  have allKeys : (boundaryValue field state.1).toNat ≤ width + 3 - 1 :=
    wide_all_valid (2 ^ width.size) (width + 3) (boundaryValue field state.1).toNat
      (by unfold narrow at wideCase; omega) (boundaryValue field state.1).isLt
  have valid : (boundaryValue field state.1).toNat ≤
      LengthBoundary.naturalConstant width field := by
    cases field <;> simp only [LengthBoundary.naturalConstant] <;> omega
  have boundaryFits : LengthBoundary.naturalConstant width field < 2 ^ length :=
    (LengthBoundary.naturalConstant_le width field).trans_lt sentinelFits
  have loadedValue : loaded.2.2.1.toNat =
      LengthBoundary.naturalConstant width field - (boundaryValue field state.1).toNat := by
    rw [LengthBoundary.prepareStep_toNat width field state prefixZero borrowZero sentinelFits,
      wrappedDifference_of_le _ _ _ boundaryFits valid]
  have loadedFits : loaded.2.2.1.toNat < 2 ^ length := loaded.2.2.1.isLt
  have loadedAddress : loaded.2.1 = state.2.1 :=
    LengthBoundary.prepareStep_address width field state
  have loadedBorrow : loaded.2.2.2 = false :=
    (LengthBoundary.prepareStep_conjunction width field state).trans borrowZero
  have controlRead : (LengthCopy.active width false).get done = state.1.control :=
    (LengthDifference.step_original width length le_rfl loaded
      (SharedEEA.controlBit width)).trans
      (LengthBoundary.prepareStep_original width field state (SharedEEA.controlBit width))
  have fullPrefix : LengthDifference.value width length true loaded = loaded.2.2.1 := by
    exact BitVec.extractLsb'_eq_self
  have fullAddress : LengthDifference.value width length false loaded = loaded.2.1 := by
    exact BitVec.extractLsb'_eq_self
  have borrowRead : done.2.2.2 = decide (loaded.2.2.1.toNat < state.2.1.toNat) := by
    rw [LengthDifference.step_borrow, loadedBorrow, Bool.false_xor, fullPrefix, fullAddress,
      loadedAddress]
  have donePrefix : done.2.2.1 = loaded.2.2.1 - loaded.2.1 := by
    have read := LengthDifference.step_value width length le_rfl loaded
    change done.2.2.1.extractLsb' 0 (ScanMetadata.addressWidth width) =
      loaded.2.2.1.extractLsb' 0 (ScanMetadata.addressWidth width) -
        loaded.2.1.extractLsb' 0 (ScanMetadata.addressWidth width) at read
    simpa only [BitVec.extractLsb'_eq_self] using read
  have valueRead : (LengthCopy.value width done).toNat =
      wrappedDifference (2 ^ length) loaded.2.2.1.toNat state.2.1.toNat % 2 ^ width.size := by
    change (done.2.2.1.extractLsb' 0 width.size).toNat = _
    rw [low_toNat, donePrefix, subtraction_toNat, loadedAddress]
  rw [actual]
  have maskRead : (LengthCopy.mask width false done).toNat =
      if state.1.control && !(decide (loaded.2.2.1.toNat < state.2.1.toNat)) then
        wrappedDifference (2 ^ length) loaded.2.2.1.toNat state.2.1.toNat % 2 ^ width.size
      else 0 := by
    unfold LengthCopy.mask
    change (if (LengthCopy.active width false).get done && !done.2.2.2 then
      LengthCopy.value width done else 0).toNat = _
    rw [controlRead, borrowRead]
    split
    · exact valueRead
    · rfl
  rw [maskRead, copiedDifference _ _ _ _ _ loadedFits, loadedValue]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthClip
