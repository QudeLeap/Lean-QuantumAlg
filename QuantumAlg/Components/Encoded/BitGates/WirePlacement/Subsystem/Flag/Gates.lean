/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Flag
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates.Equations

/-! # Native source gates beside the same existing arbitrary output flag -/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target}

private lemma lifted_ne (first second : EncodedBit source)
    (different : first.wire ≠ second.wire) :
    (BinaryLabelEncoding.prodLeftBit source .bool first).wire ≠
      (BinaryLabelEncoding.prodLeftBit source .bool second).wire := by
  intro same
  apply different
  exact Fin.ext (congrArg (fun index : Fin (source.width + 1) => index.val) same)

/-- Lift a source native instruction while keeping the supplied output flag untouched. -/
def withFlagGate : GateSpec source → GateSpec (.prod source .bool)
  | .x bit => .x (BinaryLabelEncoding.prodLeftBit source .bool bit)
  | .cnot control bit different =>
      .cnot (BinaryLabelEncoding.prodLeftBit source .bool control)
        (BinaryLabelEncoding.prodLeftBit source .bool bit) (lifted_ne _ _ different)
  | .toffoli first second bit distinct firstTarget secondTarget =>
      .toffoli (BinaryLabelEncoding.prodLeftBit source .bool first)
        (BinaryLabelEncoding.prodLeftBit source .bool second)
        (BinaryLabelEncoding.prodLeftBit source .bool bit)
        (lifted_ne _ _ distinct) (lifted_ne _ _ firstTarget) (lifted_ne _ _ secondTarget)

/-- The complete native source instruction retains the same original placement beside the flag. -/
lemma withFlag_placeGate (placement : WireSubsystem source target) (flag : EncodedBit target)
    (separate : ∀ index, placement.wires index ≠ flag.wire)
    (sourceOnto : Function.Surjective source.encode)
    (combinedOnto : Function.Surjective (BinaryLabelEncoding.prod source .bool).encode)
    (targetOnto : Function.Surjective target.encode) (gate : GateSpec source) :
    (placement.withFlag flag separate).placeGate combinedOnto targetOnto (withFlagGate gate) =
      placement.placeGate sourceOnto targetOnto gate := by
  cases gate with
  | x bit =>
      rw [withFlagGate, placeGate_x, placeGate_x]
      congr 1
      exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto bit
  | cnot control bit different =>
      rw [withFlagGate, placeGate_cnot, placeGate_cnot]
      congr 1
      · exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto
          control
      · exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto bit
  | toffoli first second bit distinct firstTarget secondTarget =>
      rw [withFlagGate, placeGate_toffoli, placeGate_toffoli]
      congr 1
      · exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto first
      · exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto
          second
      · exact placement.withFlag_place_source flag separate sourceOnto combinedOnto targetOnto bit

end

end QuantumAlg.EncodedBit.WireSubsystem
