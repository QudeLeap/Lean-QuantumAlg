/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Commutation
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.WireBit

/-! # Native subsystem action commutation on the complete physical complement -/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target}

/-- A complete placed source action commutes with XOR of physically unselected original bits. -/
lemma full_step_xorConstantStep_comm (placement : WireSubsystem source target)
    (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode) {width : Nat}
    (output : Word target width) (constant : Fin (2 ^ width))
    (outside : ∀ bit, (output.bit bit).wire ∉ Set.range placement.wires)
    (action : Source → Source) (state : Target) :
    (placement.full sourceOnto targetOnto).step (fun pair => (action pair.1, pair.2))
        (Word.xorConstantStep output constant state) =
      Word.xorConstantStep output constant
        ((placement.full sourceOnto targetOnto).step
          (fun pair => (action pair.1, pair.2)) state) := by
  apply FullPlacement.step_product_xorConstantStep_comm
    (savedOnto := Function.surjective_id)
  intro bit index same
  have mapped : (placement.full sourceOnto targetOnto).mappedWire
      (Fin.castAdd placement.complementWidth index) = placement.wires index := by
    have physical := FullPlacement.ofWires_placeBit_wire placement.paddedEncoding target
      (placement.paddedEncoding_surjective sourceOnto) targetOnto placement.completedWires
      (BinaryLabelEncoding.prodLeftBit source
        (BinaryLabelEncoding.finIdentity placement.complementWidth) (fullBit sourceOnto index))
    exact physical.trans (placement.completedWires_source index)
  exact outside bit ⟨index, mapped.symm.trans same⟩

end

end QuantumAlg.EncodedBit.WireSubsystem
