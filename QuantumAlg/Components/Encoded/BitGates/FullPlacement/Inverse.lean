/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Inverse complete physical frame certificates

Every semantic coordinate and actual physical position is inverted
together. These certificates construct no executed permutation. An
actual alignment program and its paid inverse remain separate proofs.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target}

/-- A complete original physical address map is a genuine finite wire bijection. -/
def wireEquiv (whole : FullPlacement source target) : Fin source.width ≃ Fin target.width :=
  Equiv.ofBijective whole.mappedWire ⟨whole.mappedWire_injective, whole.wire_surjective⟩

/-- Invert semantic grouping and the very same complete physical wire bijection. -/
def inverse (whole : FullPlacement source target) : FullPlacement target source :=
  ofGrouping target source whole.grouping.symm whole.wireEquiv.symm (by
    intro state index
    have encoded := whole.basis_encode (whole.grouping.symm state)
    rw [Equiv.apply_symm_apply] at encoded
    have coordinates := whole.basis_position (source.encode state) (whole.wireEquiv.symm index)
    change (BinaryBasis.bigEndianEquiv target.width).symm (whole.basis (source.encode state))
      (whole.wireEquiv (whole.wireEquiv.symm index)) = _ at coordinates
    rw [encoded, Equiv.apply_symm_apply] at coordinates
    exact coordinates.symm)

/-- The inverse certificate has exactly the supplied whole inverse grouping. -/
lemma inverse_grouping (whole : FullPlacement source target) :
    whole.inverse.grouping = whole.grouping.symm := rfl

/-- Every original physical position is inverted by the same actual finite wire map. -/
lemma inverse_mappedWire (whole : FullPlacement source target) (index : Fin target.width) :
    whole.inverse.mappedWire index = whole.wireEquiv.symm index := by
  apply Fin.ext
  change wireAddress target source whole.wireEquiv.symm index.val = _
  exact dif_pos index.isLt

/-- Complete inverse coordinates retain the entire target and original frame. -/
lemma inverse_step (whole : FullPlacement source target) (action : Target → Target)
    (state : Source) :
    whole.inverse.step action state = whole.grouping (action (whole.grouping.symm state)) := rfl

end

end QuantumAlg.EncodedBit.FullPlacement
