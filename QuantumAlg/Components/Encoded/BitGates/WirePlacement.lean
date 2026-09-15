/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Full native placement induced by actual wire coordinates

An explicit bijection of physical bit positions determines the complete
basis map and its field grouping together. Each source bit is proved to
read the corresponding target wire. The existing placement engine then
transports an actual program with its unchanged events and full frame.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type}
variable (source : BinaryLabelEncoding Source) (target : BinaryLabelEncoding Target)

/-- Reindex the complete binary coordinates by their explicit physical wire bijection. -/
def wireBasis (wires : Fin source.width ≃ Fin target.width) :
    (Qubits source.width).Index ≃ (Qubits target.width).Index :=
  (BinaryBasis.bigEndianEquiv source.width).symm.trans
    ((Equiv.arrowCongr wires (Equiv.refl (Fin 2))).trans
      (BinaryBasis.bigEndianEquiv target.width))

/-- The transported source bit has exactly its original value on the named target wire. -/
theorem wireBasis_bit (wires : Fin source.width ≃ Fin target.width)
    (label : (Qubits source.width).Index) (index : Fin source.width) :
    (wireBasis source target wires label).val.testBit (wires index).rev.val =
      label.val.testBit index.rev.val := by
  rw [wireBasis, Equiv.trans_apply, Equiv.trans_apply, BinaryBasis.bigEndianEquiv_bit]
  change finTwoEquiv ((BinaryBasis.bigEndianEquiv source.width).symm label
    (wires.symm (wires index))) = _
  rw [Equiv.symm_apply_apply, BinaryBasis.bigEndianEquiv_symm_value,
    Equiv.apply_symm_apply]

private def totalEncoding {Data : Type} (encoding : BinaryLabelEncoding Data)
    (onto : Function.Surjective encoding.encode) :
    Data ≃ (Qubits encoding.width).Index :=
  Equiv.ofBijective encoding.encode ⟨encoding.encode_injective, onto⟩

/-- Extend actual finite wire addresses to the natural labels stored by the circuit syntax. -/
def wireAddress (wires : Fin source.width ≃ Fin target.width) (index : Nat) : Nat :=
  if bound : index < source.width then (wires ⟨index, bound⟩).val else index

/-- Full field and basis placement, both derived from the same actual physical coordinates. -/
def ofWires (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (wires : Fin source.width ≃ Fin target.width) : FullPlacement source target where
  grouping := (totalEncoding target targetOnto).trans
    ((wireBasis source target wires).symm.trans (totalEncoding source sourceOnto).symm)
  basis := wireBasis source target wires
  basis_encode := by
    intro state
    change wireBasis source target wires
      (totalEncoding source sourceOnto ((totalEncoding source sourceOnto).symm
        ((wireBasis source target wires).symm (totalEncoding target targetOnto state)))) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  physicalIndex := wireAddress source target wires
  wire_injective := by
    intro left right same
    have values : (wires left).val = (wires right).val := by
      simpa only [wireAddress, dif_pos left.isLt, dif_pos right.isLt] using same
    exact wires.injective (Fin.ext values)
  wire_within := by
    intro index
    simpa only [wireAddress, dif_pos index.isLt] using (wires index).isLt

end

end QuantumAlg.EncodedBit.FullPlacement
