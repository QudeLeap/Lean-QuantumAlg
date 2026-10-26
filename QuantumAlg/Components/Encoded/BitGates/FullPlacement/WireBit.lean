/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-! # Literal placed bit coordinates of a complete wire-derived frame -/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

/-- Wire-derived native placement names exactly the declared original target coordinate. -/
lemma ofWires_placeBit_wire {Source Target : Type}
    (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target)
    (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (wires : Fin source.width ≃ Fin target.width) (bit : EncodedBit source) :
    ((ofWires source target sourceOnto targetOnto wires).placeBit bit).wire = wires bit.wire := by
  apply Fin.ext
  change wireAddress source target wires bit.wire.val = (wires bit.wire).val
  exact dif_pos bit.wire.isLt

end

end QuantumAlg.EncodedBit.FullPlacement
