/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates.Equations

/-! # Native subsystem gates exclude every original position outside the selected wires -/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target} (placement : WireSubsystem source target)

/-- Every operand of every emitted primitive lies on an actually selected subsystem wire. -/
lemma placeGate_bitDisjoint (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) (gate : GateSpec source)
    (observed : EncodedBit target)
    (outside : ∀ index, placement.wires index ≠ observed.wire) :
    GateSpec.bitDisjoint observed (placement.placeGate sourceOnto targetOnto gate) := by
  cases gate with
  | x bit =>
      simpa only [placeGate_x, GateSpec.bitDisjoint, placeBit_wire] using outside bit.wire
  | cnot control bit different =>
      simp only [placeGate_cnot, GateSpec.bitDisjoint, placeBit_wire]
      exact ⟨outside control.wire, outside bit.wire⟩
  | toffoli first second bit distinct firstTarget secondTarget =>
      simp only [placeGate_toffoli, GateSpec.bitDisjoint, placeBit_wire]
      exact ⟨outside first.wire, outside second.wire, outside bit.wire⟩

end

end QuantumAlg.EncodedBit.WireSubsystem
