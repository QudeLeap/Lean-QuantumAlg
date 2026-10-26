/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Inverse
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Append an exactly retained existing word to a complete physical frame

The original source and target groupings are unchanged and the existing
suffix has its original physical order. This is a coordinate certificate,
with no allocation or executed permutation.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Target Extra : Type} {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target}

private def appendWires (whole : FullPlacement source target) (extra : Nat) :
    Fin (source.width + extra) ≃ Fin (target.width + extra) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr whole.wireEquiv (Equiv.refl (Fin extra))).trans finSumFinEquiv)

private lemma appendWires_source (whole : FullPlacement source target) (extra : Nat)
    (index : Fin source.width) :
    whole.appendWires extra (Fin.castAdd extra index) =
      Fin.castAdd extra (whole.mappedWire index) := by
  simp only [appendWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
  rfl

private lemma appendWires_extra (whole : FullPlacement source target) (extra : Nat)
    (index : Fin extra) :
    whole.appendWires extra (Fin.natAdd source.width index) = Fin.natAdd target.width index := by
  simp only [appendWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]

/-- Retain an existing complete suffix without changing either original field grouping. -/
def appendRight (whole : FullPlacement source target) (extra : BinaryLabelEncoding Extra) :
    FullPlacement (BinaryLabelEncoding.prod source extra)
      (BinaryLabelEncoding.prod target extra) :=
  ofGrouping _ _ (Equiv.prodCongr whole.grouping (Equiv.refl Extra))
    (whole.appendWires extra.width) (by
      intro state index
      change (BinaryBasis.bigEndianEquiv (target.width + extra.width)).symm
        (prodEquiv (target.encode state.1, extra.encode state.2))
        (whole.appendWires extra.width index) =
          (BinaryBasis.bigEndianEquiv (source.width + extra.width)).symm
            (prodEquiv (source.encode (whole.grouping state.1), extra.encode state.2)) index
      refine Fin.addCases (m := source.width) (n := extra.width)
        (fun primary => ?_) (fun retained => ?_) index
      · rw [whole.appendWires_source, BinaryBasis.bigEndianEquiv_prod_left,
          BinaryBasis.bigEndianEquiv_prod_left, ← whole.basis_encode state.1]
        exact whole.basis_position (source.encode (whole.grouping state.1)) primary
      · rw [whole.appendWires_extra, BinaryBasis.bigEndianEquiv_prod_right,
          BinaryBasis.bigEndianEquiv_prod_right])

/-- The retained suffix keeps the literal original product grouping. -/
lemma appendRight_grouping (whole : FullPlacement source target)
    (extra : BinaryLabelEncoding Extra) :
    (whole.appendRight extra).grouping = Equiv.prodCongr whole.grouping (Equiv.refl Extra) := rfl

/-- Every original source coordinate keeps its original physical position. -/
lemma appendRight_mappedWire_source (whole : FullPlacement source target)
    (extra : BinaryLabelEncoding Extra) (index : Fin source.width) :
    (whole.appendRight extra).mappedWire (Fin.castAdd extra.width index) =
      Fin.castAdd extra.width (whole.mappedWire index) := by
  have position : (whole.appendRight extra).mappedWire (Fin.castAdd extra.width index) =
      whole.appendWires extra.width (Fin.castAdd extra.width index) := by
    apply Fin.ext
    exact dif_pos (Fin.castAdd extra.width index).isLt
  exact position.trans (whole.appendWires_source extra.width index)

/-- Every existing suffix coordinate keeps its original physical order. -/
lemma appendRight_mappedWire_extra (whole : FullPlacement source target)
    (extra : BinaryLabelEncoding Extra) (index : Fin extra.width) :
    (whole.appendRight extra).mappedWire (Fin.natAdd source.width index) =
      Fin.natAdd target.width index := by
  have position : (whole.appendRight extra).mappedWire (Fin.natAdd source.width index) =
      whole.appendWires extra.width (Fin.natAdd source.width index) := by
    apply Fin.ext
    exact dif_pos (Fin.natAdd source.width index).isLt
  exact position.trans (whole.appendWires_extra extra.width index)

/-- The complete existing suffix is retained under every original full-frame action. -/
lemma appendRight_step (whole : FullPlacement source target) (extra : BinaryLabelEncoding Extra)
    (action : Source → Source) (state : Target × Extra) :
    (whole.appendRight extra).step (fun pair => (action pair.1, pair.2)) state =
      (whole.step action state.1, state.2) := rfl

end

end QuantumAlg.EncodedBit.FullPlacement
