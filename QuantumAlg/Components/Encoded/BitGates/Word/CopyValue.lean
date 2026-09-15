/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Components.Control
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-! # Value semantics for encoded-word copies -/

section

namespace QuantumAlg
namespace EncodedBit
namespace Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Copying into a clean concrete word reconstructs the source value.  The
bitwise extensionality argument is kept generic in `width`, so fixed-width
clients do not have to elaborate it after specializing to a large word. -/
theorem xorIntoStep_readWord_of_clean
    (source target : Word encoding width)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (read : Data → Nat.FixedWidth.Word width)
    (hread : ∀ bit state,
      (target.bit bit).get state = (read state).val.testBit bit.val)
    (htargetTarget : ∀ left right, left ≠ right →
      (target.bit left).wire ≠ (target.bit right).wire)
    (htargetSource : ∀ sourceBit targetBit,
      (target.bit targetBit).wire ≠ (source.bit sourceBit).wire)
    (state : Data) (value : Nat.FixedWidth.Word width)
    (hclean : read state = 0)
    (hsource : ∀ bit,
      (source.bit bit).get state = value.val.testBit bit.val) :
    read (xorIntoStep source target hdisjoint state) = value := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  rw [← hread bit, xorIntoStep_get_target source target hdisjoint bit
    (fun other hne => htargetTarget other bit hne)
    (fun other => htargetSource bit other)]
  rw [hread bit, hclean, hsource bit]
  simp

/-- Reconstruct a complete state after copying a source word into a clean
target.  Clients separately expose the target value and the frame erased by
that value, avoiding normalization of the concrete word-copy fold. -/
theorem xorIntoStep_eq_set_of_clean
    {Frame : Type}
    (source target : Word encoding width)
    (hdisjoint : ∀ bit, (source.bit bit).wire ≠ (target.bit bit).wire)
    (read : Data → Nat.FixedWidth.Word width)
    (frame : Data → Frame)
    (set : Frame → Nat.FixedWidth.Word width → Data)
    (hdecompose : ∀ state, set (frame state) (read state) = state)
    (hread : ∀ bit state,
      (target.bit bit).get state = (read state).val.testBit bit.val)
    (htargetTarget : ∀ left right, left ≠ right →
      (target.bit left).wire ≠ (target.bit right).wire)
    (htargetSource : ∀ sourceBit targetBit,
      (target.bit targetBit).wire ≠ (source.bit sourceBit).wire)
    (hframe : ∀ bit state, frame ((target.bit bit).flip state) = frame state)
    (state : Data) (value : Nat.FixedWidth.Word width)
    (hclean : read state = 0)
    (hsource : ∀ bit,
      (source.bit bit).get state = value.val.testBit bit.val) :
    xorIntoStep source target hdisjoint state =
      set (frame state) value := by
  let result := xorIntoStep source target hdisjoint state
  have hresultFrame : frame result = frame state := by
    exact xorIntoStep_preserves_projection
      source target hdisjoint frame hframe state
  have hresultWord : read result = value := by
    exact xorIntoStep_readWord_of_clean
      source target hdisjoint read hread htargetTarget htargetSource
        state value hclean hsource
  calc
    result = set (frame result) (read result) := (hdecompose result).symm
    _ = set (frame state) value := congrArg₂ set hresultFrame hresultWord

end Word
end EncodedBit
end QuantumAlg

end
