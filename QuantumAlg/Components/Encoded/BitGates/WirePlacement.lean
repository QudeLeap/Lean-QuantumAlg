/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement
import all QuantumAlg.Components.Encoded.BitGates.Basic
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

/-- Construct a full placement from a semantic grouping checked on each actual wire. -/
def ofGrouping (grouping : Target ≃ Source)
    (wires : Fin source.width ≃ Fin target.width)
    (coordinates : ∀ state index,
      (BinaryBasis.bigEndianEquiv target.width).symm (target.encode state) (wires index) =
        (BinaryBasis.bigEndianEquiv source.width).symm
          (source.encode (grouping state)) index) : FullPlacement source target where
  grouping := grouping
  basis := wireBasis source target wires
  basis_encode := by
    intro state
    apply (BinaryBasis.bigEndianEquiv target.width).symm.injective
    funext position
    obtain ⟨index, rfl⟩ := wires.surjective position
    change (BinaryBasis.bigEndianEquiv target.width).symm
      (BinaryBasis.bigEndianEquiv target.width
        (fun position => (BinaryBasis.bigEndianEquiv source.width).symm
          (source.encode (grouping state)) (wires.symm position))) (wires index) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact (coordinates state index).symm
  physicalIndex := wireAddress source target wires
  wire_injective := by
    intro left right same
    apply wires.injective
    apply Fin.ext
    simpa only [wireAddress, dif_pos left.isLt, dif_pos right.isLt] using same
  wire_within := by
    intro index
    simpa only [wireAddress, dif_pos index.isLt] using (wires index).isLt
  wire_surjective := by
    intro index
    refine ⟨wires.symm index, ?_⟩
    apply Fin.ext
    simp [wireAddress]
  basis_position := by
    intro label index
    have position :
        (⟨wireAddress source target wires index.val,
          by simpa only [wireAddress, dif_pos index.isLt] using (wires index).isLt⟩ :
            Fin target.width) = wires index := by
      apply Fin.ext
      simp [wireAddress]
    apply finTwoEquiv.injective
    rw [BinaryBasis.bigEndianEquiv_symm_value,
      BinaryBasis.bigEndianEquiv_symm_value]
    simp only [Equiv.apply_symm_apply]
    rw [position]
    exact wireBasis_bit source target wires label index

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
  wire_surjective := by
    intro index
    refine ⟨wires.symm index, ?_⟩
    apply Fin.ext
    simp [wireAddress]
  basis_position := by
    intro label index
    have position :
        (⟨wireAddress source target wires index.val,
          by simpa only [wireAddress, dif_pos index.isLt] using (wires index).isLt⟩ :
            Fin target.width) = wires index := by
      apply Fin.ext
      simp [wireAddress]
    apply finTwoEquiv.injective
    rw [BinaryBasis.bigEndianEquiv_symm_value,
      BinaryBasis.bigEndianEquiv_symm_value]
    simp only [Equiv.apply_symm_apply]
    rw [position]
    exact wireBasis_bit source target wires label index

/-- A bit read through a wire-derived grouping equals the bit at its named target wire. -/
theorem ofWires_read (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (wires : Fin source.width ≃ Fin target.width)
    (sourceBit : _root_.QuantumAlg.EncodedBit source)
    (targetBit : _root_.QuantumAlg.EncodedBit target)
    (same : wires sourceBit.wire = targetBit.wire) (state : Target) :
    sourceBit.get ((ofWires source target sourceOnto targetOnto wires).grouping state) =
      targetBit.get state := by
  have sourceRead (value : Source) :
      sourceBit.get value =
        (source.encode value).val.testBit sourceBit.wire.rev.val := by
    rw [← sourceBit.get_eq]
    apply congrArg (fun position => (source.encode value).val.testBit position)
    dsimp only [WireAddress.bitIndex, Fin.rev]
    omega
  have targetRead (value : Target) :
      targetBit.get value =
        (target.encode value).val.testBit targetBit.wire.rev.val := by
    rw [← targetBit.get_eq]
    apply congrArg (fun position => (target.encode value).val.testBit position)
    dsimp only [WireAddress.bitIndex, Fin.rev]
    omega
  rw [sourceRead, targetRead]
  have encoded :=
    (ofWires source target sourceOnto targetOnto wires).basis_encode state
  change wireBasis source target wires
    (source.encode ((ofWires source target sourceOnto targetOnto wires).grouping state)) =
      target.encode state at encoded
  have actual := wireBasis_bit source target wires
    (source.encode ((ofWires source target sourceOnto targetOnto wires).grouping state))
    sourceBit.wire
  rw [encoded, same] at actual
  exact actual.symm

/-- Regroup semantic fields whose binary labels and physical positions already coincide. -/
def ofEqualWidth (grouping : Target ≃ Source) (sameWidth : source.width = target.width)
    (sameLabels : ∀ state,
      Fin.cast (congrArg (fun width => 2 ^ width) sameWidth)
        (source.encode (grouping state)) = target.encode state) : FullPlacement source target := by
  rcases source with ⟨sourceWidth, sourceEncode, sourceInjective⟩
  rcases target with ⟨targetWidth, targetEncode, targetInjective⟩
  dsimp only at sameWidth sameLabels
  subst targetWidth
  apply ofGrouping _ _ grouping (Equiv.refl _)
  intro state index
  have labels : sourceEncode (grouping state) = targetEncode state := sameLabels state
  exact congrArg
    (fun label => (BinaryBasis.bigEndianEquiv sourceWidth).symm label index) labels.symm

/-- Equal-width transport retains the supplied semantic grouping exactly. -/
@[simp] theorem ofEqualWidth_grouping (grouping : Target ≃ Source)
    (sameWidth : source.width = target.width)
    (sameLabels : ∀ state,
      Fin.cast (congrArg (fun width => 2 ^ width) sameWidth)
        (source.encode (grouping state)) = target.encode state) :
    (ofEqualWidth source target grouping sameWidth sameLabels).grouping = grouping := by
  rcases source with ⟨sourceWidth, sourceEncode, sourceInjective⟩
  rcases target with ⟨targetWidth, targetEncode, targetInjective⟩
  dsimp only at sameWidth sameLabels
  subst targetWidth
  rfl

end

end QuantumAlg.EncodedBit.FullPlacement
