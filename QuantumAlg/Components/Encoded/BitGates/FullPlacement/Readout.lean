/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Word readouts from the physical wires of an existing complete placement

These laws use the supplied placement directly. Its semantic grouping is
never compared with a second constructed grouping. Each read follows from
the same physical position that transports the actual native program.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target}

/-- Equal actual wire positions identify the readout of a transported source bit. -/
lemma read_of_placeBit_wire (whole : FullPlacement source target)
    (sourceBit : EncodedBit source) (targetBit : EncodedBit target)
    (location : (whole.placeBit sourceBit).wire = targetBit.wire) (state : Target) :
    sourceBit.get (whole.grouping state) = targetBit.get state := by
  have lenses : whole.placeBit sourceBit = targetBit := eq_of_wire_eq _ _ location
  exact congrArg (fun bit : EncodedBit target => bit.get state) lenses

/-- A finite word is determined by its actual most-significant-first physical readouts. -/
lemma read_fin_of_placeBit_wires (whole : FullPlacement source target) {width : Nat}
    (project : Source → Fin (2 ^ width))
    (sourceBits : Fin width → EncodedBit source)
    (targetBits : Fin width → EncodedBit target)
    (sourceReads : ∀ state index, (sourceBits index).get state =
      (BitVec.ofFin (project state)).getMsbD index.val)
    (locations : ∀ index, (whole.placeBit (sourceBits index)).wire =
      (targetBits index).wire)
    (state : Target) (value : Fin (2 ^ width))
    (targetReads : ∀ index, (targetBits index).get state =
      (BitVec.ofFin value).getMsbD index.val) :
    project (whole.grouping state) = value := by
  have same : BitVec.ofFin (project (whole.grouping state)) = BitVec.ofFin value := by
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    exact (sourceReads _ ⟨index, within⟩).symm.trans
      ((whole.read_of_placeBit_wire (sourceBits ⟨index, within⟩)
        (targetBits ⟨index, within⟩) (locations ⟨index, within⟩) state).trans
          (targetReads ⟨index, within⟩))
  exact congrArg BitVec.toFin same

end

end QuantumAlg.EncodedBit.FullPlacement
