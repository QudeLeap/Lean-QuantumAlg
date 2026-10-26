/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Commutation

/-! # Retained high active flag and original-output commutation of the actual low difference -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The narrow actual subtraction leaves the high existing address activation unchanged. -/
lemma step_active (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (strict : length < ScanMetadata.addressWidth width) (state : Data width) :
    (LengthCopy.active width true).get (step width length fits state) =
      (LengthCopy.active width true).get state := by
  apply step_get_of_outside
  · intro position
    apply address_address_ne
    intro same
    have values := congrArg Fin.val same
    change ScanMetadata.addressWidth width - length + position.val = 0 at values
    omega
  · intro position
    exact (address_prefix_ne width _ _).symm
  · exact (address_conjunction_ne width _).symm

/-- The complete actual pool subtraction commutes with any XOR into either original length. -/
lemma step_output_comm (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (field : Field) (constant : Fin (2 ^ width.size)) (state : Data width) :
    step width length fits (Word.xorConstantStep (LengthCopy.target width field) constant state) =
      Word.xorConstantStep (LengthCopy.target width field) constant
        (step width length fits state) := by
  apply WireSubsystem.full_step_xorConstantStep_comm
    (sourceOnto := source_onto length) (targetOnto := encoding_surjective width)
  intro bit
  apply outside_subsystem
  · intro position
    exact (source_address_ne width (outputBit width field bit) _).symm
  · intro position
    exact (source_prefix_ne width (outputBit width field bit) _).symm
  · exact (source_conjunction_ne width (outputBit width field bit)).symm

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
