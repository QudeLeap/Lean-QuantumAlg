/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Encoder
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Encoder.Commutation

/-!
# Native policy encoder commutation on every encoded state

The original metadata target is outside the true source/output/prefix
fields. Both actual native programs have identical complete actions on
all inputs; arbitrary restored bank values need no additional promise.
-/

namespace QuantumAlg.EncodedBit.FirstOne.TestPolicy

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)

/-- Complete actual policy execution commutes with outside metadata XOR
without prefix cleanliness. -/
lemma policyEncoderStepList_xorConstantStep_comm {metadataWidth : Nat}
    (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth)
    (metadata : Word encoding metadataWidth) (constant : Fin (2 ^ metadataWidth))
    (sourceOutside : ∀ source target,
      (frame.source.bit source).wire ≠ (metadata.bit target).wire)
    (outputOutside : ∀ output target,
      (frame.output.bit output).wire ≠ (metadata.bit target).wire)
    (stackOutside : ∀ stack target,
      (frame.stack.bit stack).wire ≠ (metadata.bit target).wire) (state : Data) :
    GateSpec.stepList (policy.encoderGates height capacity fits)
        (Word.xorConstantStep metadata constant state) =
      Word.xorConstantStep metadata constant
        (GateSpec.stepList (policy.encoderGates height capacity fits) state) := by
  rw [policy.policyEncoderGates_eq_original, policy.policyEncoderGates_eq_original]
  exact frame.encoderStepList_xorConstantStep_comm height capacity fits metadata constant
    sourceOutside outputOutside stackOutside state

end

end QuantumAlg.EncodedBit.FirstOne.TestPolicy
