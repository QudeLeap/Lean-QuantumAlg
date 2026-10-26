/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Product
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Identical complete subsystem actions under different saved-frame coordinates

The source physical positions agree literally. Every other original
physical coordinate is retained by both mathematical frame actions.
Their complete outputs are equal regardless of how the saved positions
are encoded or ordered. Actual circuit realization remains a separate
obligation; this theorem constructs no gate or program from an action.
-/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Saved Target : Type}
    {source : BinaryLabelEncoding Source} {saved : BinaryLabelEncoding Saved}
    {target : BinaryLabelEncoding Target}

/-- Both complete groupings read exactly the same original physical source component. -/
lemma grouping_source_eq_fullFrame (placement : WireSubsystem source target)
    (sourceOnto : Function.Surjective source.encode)
    (targetOnto : Function.Surjective target.encode)
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (agree : ∀ index : Fin source.width,
      whole.mappedWire (Fin.castAdd saved.width index) = placement.wires index)
    (state : Target) :
    ((placement.full sourceOnto targetOnto).grouping state).1 = (whole.grouping state).1 := by
  apply state_eq_of_get_eq sourceOnto
  intro bit
  have location : placement.wires bit.wire =
      (whole.placeBit (BinaryLabelEncoding.prodLeftBit source saved bit)).wire := by
    change placement.wires bit.wire = whole.mappedWire (Fin.castAdd saved.width bit.wire)
    exact (agree bit.wire).symm
  exact placement.full_source_read sourceOnto targetOnto bit
    (whole.placeBit (BinaryLabelEncoding.prodLeftBit source saved bit)) location state

/-- Exact source positions and the entire physical complement determine the same full action. -/
lemma full_step_eq_fullFrame (placement : WireSubsystem source target)
    (sourceOnto : Function.Surjective source.encode)
    (savedOnto : Function.Surjective saved.encode)
    (targetOnto : Function.Surjective target.encode)
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (agree : ∀ index : Fin source.width,
      whole.mappedWire (Fin.castAdd saved.width index) = placement.wires index)
    (action : Source → Source) (state : Target) :
    (placement.full sourceOnto targetOnto).step (fun pair => (action pair.1, pair.2)) state =
      whole.step (fun pair => (action pair.1, pair.2)) state := by
  apply state_eq_of_get_eq targetOnto
  intro observed
  by_cases inside : observed.wire ∈ Set.range placement.wires
  · obtain ⟨wire, location⟩ := inside
    let bit := fullBit sourceOnto wire
    have selected : placement.wires bit.wire = observed.wire := location
    have left := placement.full_step_source_read sourceOnto targetOnto bit observed selected
      action state
    rw [placement.grouping_source_eq_fullFrame sourceOnto targetOnto whole agree state] at left
    have lenses : whole.placeBit (BinaryLabelEncoding.prodLeftBit source saved bit) =
        observed := by
      apply eq_of_wire_eq
      change whole.mappedWire (Fin.castAdd saved.width wire) = observed.wire
      exact (agree wire).trans location
    have right := whole.step_product_source_read action bit state
    rw [lenses] at right
    exact left.trans right.symm
  · have retained : ∀ index : Fin source.width,
        whole.mappedWire (Fin.castAdd saved.width index) ≠ observed.wire := by
      intro index same
      exact inside ⟨index, (agree index).symm.trans same⟩
    exact (placement.full_step_other_read sourceOnto targetOnto observed inside action state).trans
      (whole.step_product_get_of_prefix_ne savedOnto observed retained action state).symm

end

end QuantumAlg.EncodedBit.WireSubsystem
