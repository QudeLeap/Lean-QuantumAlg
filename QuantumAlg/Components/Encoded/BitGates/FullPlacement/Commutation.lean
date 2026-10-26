/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Product
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-! # Full subsystem actions commute with changes to their actual retained complement -/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Saved Target : Type}
    {source : BinaryLabelEncoding Source} {saved : BinaryLabelEncoding Saved}
    {target : BinaryLabelEncoding Target}

/-- A source action commutes with a real flip at any original complementary physical wire. -/
lemma step_product_flip_comm
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (savedOnto : Function.Surjective saved.encode) (observed : EncodedBit target)
    (outside : ∀ index : Fin source.width,
      whole.mappedWire (Fin.castAdd saved.width index) ≠ observed.wire)
    (action : Source → Source) (state : Target) :
    whole.step (fun pair => (action pair.1, pair.2)) (observed.flip state) =
      observed.flip (whole.step (fun pair => (action pair.1, pair.2)) state) := by
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
      simp only [placeBit, step, Equiv.apply_symm_apply]
      rfl

/-- The same full action commutes with any finite XOR into an entirely retained output word. -/
lemma step_product_xorConstantStep_comm
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (savedOnto : Function.Surjective saved.encode) {width : Nat}
    (output : Word target width) (constant : Fin (2 ^ width))
    (outside : ∀ bit index,
      whole.mappedWire (Fin.castAdd saved.width index) ≠ (output.bit bit).wire)
    (action : Source → Source) (state : Target) :
    whole.step (fun pair => (action pair.1, pair.2))
        (Word.xorConstantStep output constant state) =
      Word.xorConstantStep output constant
        (whole.step (fun pair => (action pair.1, pair.2)) state) := by
  rw [Word.xorConstantStep_eq_indicesStep]
  have commute (indices : List (Fin width)) (state : Target) :
      whole.step (fun pair => (action pair.1, pair.2))
          (Word.xorConstantIndicesStep output indices state) =
        Word.xorConstantIndicesStep output indices
          (whole.step (fun pair => (action pair.1, pair.2)) state) := by
    induction indices generalizing state with
    | nil => rfl
    | cons bit rest ih =>
        change whole.step (fun pair => (action pair.1, pair.2))
          (Word.xorConstantIndicesStep output rest ((output.bit bit).flip state)) = _
        rw [ih, whole.step_product_flip_comm savedOnto (output.bit bit) (outside bit)]
        rfl
  exact commute _ state

end

end QuantumAlg.EncodedBit.FullPlacement
