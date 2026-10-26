/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-! # Complete source and retained-product readouts under a physical full-frame placement -/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Saved Target : Type}
    {source : BinaryLabelEncoding Source} {saved : BinaryLabelEncoding Saved}
    {target : BinaryLabelEncoding Target}

/-- An original source lens reads its actual selected component in the complete grouping. -/
lemma product_source_read (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (bit : EncodedBit source) (state : Target) :
    (whole.placeBit (BinaryLabelEncoding.prodLeftBit source saved bit)).get state =
      bit.get (whole.grouping state).1 := rfl

/-- The actual selected component changes by precisely the supplied full source action. -/
lemma step_product_source_read
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (action : Source → Source) (bit : EncodedBit source) (state : Target) :
    (whole.placeBit (BinaryLabelEncoding.prodLeftBit source saved bit)).get
        (whole.step (fun pair => (action pair.1, pair.2)) state) =
      bit.get (action (whole.grouping state).1) := by
  simp only [placeBit, step, Equiv.apply_symm_apply]
  rfl

/-- All actual saved-product coordinates retain their complete original values. -/
lemma step_product_saved_read
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (action : Source → Source) (bit : EncodedBit saved) (state : Target) :
    (whole.placeBit (BinaryLabelEncoding.prodRightBit source saved bit)).get
        (whole.step (fun pair => (action pair.1, pair.2)) state) =
      (whole.placeBit (BinaryLabelEncoding.prodRightBit source saved bit)).get state := by
  simp only [placeBit, step, Equiv.apply_symm_apply]
  rfl

/-- A complete source action keeps every original physical bit outside its selected prefix. -/
lemma step_product_get_of_prefix_ne
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (savedOnto : Function.Surjective saved.encode) (observed : EncodedBit target)
    (outside : ∀ index : Fin source.width,
      whole.mappedWire (Fin.castAdd saved.width index) ≠ observed.wire)
    (action : Source → Source) (state : Target) :
    observed.get (whole.step (fun pair => (action pair.1, pair.2)) state) =
      observed.get state := by
  obtain ⟨wire, same⟩ := whole.wire_surjective observed.wire
  change whole.mappedWire wire = observed.wire at same
  obtain ⟨selected, rfl⟩ := finSumFinEquiv.surjective wire
  cases selected with
  | inl index => exact False.elim (outside index same)
  | inr index =>
      let bit := BinaryLabelEncoding.prodRightBit source saved (fullBit savedOnto index)
      have location : (whole.placeBit bit).wire = observed.wire := same
      have lenses : whole.placeBit bit = observed := eq_of_wire_eq _ _ location
      rw [← lenses]
      exact whole.step_product_saved_read action (fullBit savedOnto index) state

end

end QuantumAlg.EncodedBit.FullPlacement
