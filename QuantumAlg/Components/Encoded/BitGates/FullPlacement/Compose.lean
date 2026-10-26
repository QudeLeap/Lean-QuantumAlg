/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Compose complete frames through the same actual physical positions

Semantic grouping and every native address are composed together. The
result is a complete frame certificate, with no additional executed gate.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Middle Target : Type}
    {source : BinaryLabelEncoding Source} {middle : BinaryLabelEncoding Middle}
    {target : BinaryLabelEncoding Target}

/-- Compose both semantic coordinates and literal original physical addresses. -/
def compose (inner : FullPlacement source middle) (outer : FullPlacement middle target) :
    FullPlacement source target where
  grouping := outer.grouping.trans inner.grouping
  basis := inner.basis.trans outer.basis
  basis_encode := by
    intro state
    change outer.basis (inner.basis (source.encode
      (inner.grouping (outer.grouping state)))) = target.encode state
    rw [inner.basis_encode, outer.basis_encode]
  physicalIndex index := outer.physicalIndex (inner.physicalIndex index)
  wire_injective := by
    intro left right same
    apply inner.wire_injective
    have positions := outer.wire_injective (a₁ := inner.mappedWire left)
      (a₂ := inner.mappedWire right) same
    exact congrArg Fin.val positions
  wire_within index := outer.wire_within (inner.mappedWire index)
  wire_surjective := by
    intro index
    obtain ⟨middleIndex, middleSame⟩ := outer.wire_surjective index
    obtain ⟨sourceIndex, sourceSame⟩ := inner.wire_surjective middleIndex
    change inner.mappedWire sourceIndex = middleIndex at sourceSame
    change outer.mappedWire middleIndex = index at middleSame
    refine ⟨sourceIndex, ?_⟩
    change outer.mappedWire (inner.mappedWire sourceIndex) = index
    rw [sourceSame]
    exact middleSame
  basis_position := by
    intro label index
    change (BinaryBasis.bigEndianEquiv target.width).symm (outer.basis (inner.basis label))
      (outer.mappedWire (inner.mappedWire index)) = _
    exact (outer.basis_position (inner.basis label) (inner.mappedWire index)).trans
      (inner.basis_position label index)

/-- Every selected coordinate passes through the same two original physical maps. -/
lemma compose_mappedWire (inner : FullPlacement source middle)
    (outer : FullPlacement middle target) (index : Fin source.width) :
    (inner.compose outer).mappedWire index = outer.mappedWire (inner.mappedWire index) := rfl

/-- Complete semantic action follows the same two groupings, including all complements. -/
lemma compose_step (inner : FullPlacement source middle)
    (outer : FullPlacement middle target) (action : Source → Source) (state : Target) :
    (inner.compose outer).step action state = outer.step (inner.step action) state := rfl

end

end QuantumAlg.EncodedBit.FullPlacement
