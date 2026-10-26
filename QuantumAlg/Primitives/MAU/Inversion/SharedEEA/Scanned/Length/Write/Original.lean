/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Write
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Prepare.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Mask

/-!
# Complete actual native length write equals the original region-size XOR

The zero-pool boundary and the full sentinel fit are explicit. Original
work, metadata, control, target and Iter remain arbitrary. Actual full
preparation, paid native copy and adjoint cleanup yield the complete
original finite value action, retaining every other physical input.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma step_eq_mask (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width) (state : Data width) :
    step width field first capacity state =
      Word.xorConstantStep (LengthCopy.target width field)
        (LengthCopy.mask width (decide (LengthClip.narrow width))
          (LengthPrepare.step width field first capacity state)).toFin state := by
  unfold step LengthCopy.mask
  dsimp only
  split
  · rfl
  · exact (LengthCopy.xorConstantStep_zero width field state).symm

/-- The complete native write's finite action is exactly the original selected region size. -/
lemma step_eq_original (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    step width field first capacity state =
      if state.1.control then Word.xorConstantStep (LengthCopy.target width field)
        (BitVec.ofNat width.size
          (LengthRead.payloadValue field (boundaryValue field state.1) first state.1).size).toFin
        state else state := by
  rw [step_eq_mask, LengthPrepare.mask_eq_original width field first capacity state
    prefixZero addressZero borrowZero sentinelFits]
  split
  · rfl
  · exact LengthCopy.xorConstantStep_zero width field state

/-- The actual whole program has this complete original ket action with no arithmetic promise. -/
lemma program_apply_encoded_ket_original (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (borrowZero : state.2.2.2 = false)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (program width field first capacity).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode
          (if state.1.control then Word.xorConstantStep (LengthCopy.target width field)
            (BitVec.ofNat width.size
              (LengthRead.payloadValue field (boundaryValue field state.1) first
                state.1).size).toFin
            state else state))) := by
  have actual := (program_realizes width field first capacity environment).apply_encoded_ket state
  rw [step_eq_original width field first capacity state prefixZero addressZero borrowZero
    sentinelFits] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthRefreshWrite
