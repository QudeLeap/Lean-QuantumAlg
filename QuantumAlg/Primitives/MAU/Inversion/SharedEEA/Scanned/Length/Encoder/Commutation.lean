/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Commutation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Commutation

/-! # Actual EEA first-one encoding commutes with the independent original length output -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Native tests and visits commute with the original target XOR, even on dirty prefixes. -/
lemma gates_output_comm (width : Nat) (field : Field) (first : Bool) (height : Nat)
    (capacity : width + 3 ≤ 2 ^ height) (fits : height ≤ ScanMetadata.addressWidth width)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    GateSpec.stepList ((frame width field first).encoderGates height capacity fits)
        (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (GateSpec.stepList ((frame width field first).encoderGates height capacity fits)
          state) := by
  apply FirstOne.Frame.encoderStepList_xorConstantStep_comm
  · intro input output
    exact LengthAlignment.word_output width field first
      (LengthAlignment.priorityIndex width field input) output
  · intro input output
    exact (source_address_ne width (outputBit width field output) input.rev).symm
  · intro input output
    change (SelectionFrame.stack width input).wire ≠
      (sourceBit width (outputBit width field output)).wire
    unfold SelectionFrame.stack
    split
    · exact LengthCopy.active_target width false field output
    · exact (source_prefix_ne width (outputBit width field output) _).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
