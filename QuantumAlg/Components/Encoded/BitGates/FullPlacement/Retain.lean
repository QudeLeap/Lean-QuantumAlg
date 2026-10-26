/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-! # Extend a complete original physical frame by an exactly retained existing suffix -/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

variable {Source Saved Target Extra : Type}
    {source : BinaryLabelEncoding Source} {saved : BinaryLabelEncoding Saved}
    {target : BinaryLabelEncoding Target}

private def completeWires
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) :
    Fin (source.width + saved.width) ≃ Fin target.width :=
  Equiv.ofBijective whole.mappedWire ⟨whole.mappedWire_injective, whole.wire_surjective⟩

private def retainedWires
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) (extra : Nat) :
    Fin (source.width + (saved.width + extra)) ≃ Fin (target.width + extra) :=
  (finCongr (Nat.add_assoc source.width saved.width extra).symm).trans
    (finSumFinEquiv.symm.trans
      ((Equiv.sumCongr whole.completeWires (Equiv.refl (Fin extra))).trans finSumFinEquiv))

private lemma retainedWires_source
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) (extra : Nat)
    (index : Fin source.width) :
    whole.retainedWires extra (Fin.castAdd (saved.width + extra) index) =
      Fin.castAdd extra (whole.mappedWire (Fin.castAdd saved.width index)) := by
  have regroup : finCongr (Nat.add_assoc source.width saved.width extra).symm
      (Fin.castAdd (saved.width + extra) index) =
      Fin.castAdd extra (Fin.castAdd saved.width index) := Fin.ext rfl
  simp only [retainedWires, Equiv.trans_apply, regroup,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, completeWires]
  rfl

private lemma retainedWires_saved
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) (extra : Nat)
    (index : Fin saved.width) :
    whole.retainedWires extra (Fin.natAdd source.width (Fin.castAdd extra index)) =
      Fin.castAdd extra (whole.mappedWire (Fin.natAdd source.width index)) := by
  have regroup : finCongr (Nat.add_assoc source.width saved.width extra).symm
      (Fin.natAdd source.width (Fin.castAdd extra index)) =
      Fin.castAdd extra (Fin.natAdd source.width index) := Fin.ext rfl
  simp only [retainedWires, Equiv.trans_apply, regroup,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, completeWires]
  rfl

private lemma retainedWires_extra
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target) (extra : Nat)
    (index : Fin extra) :
    whole.retainedWires extra (Fin.natAdd source.width (Fin.natAdd saved.width index)) =
      Fin.natAdd target.width index := by
  have regroup : finCongr (Nat.add_assoc source.width saved.width extra).symm
      (Fin.natAdd source.width (Fin.natAdd saved.width index)) =
      Fin.natAdd (source.width + saved.width) index := by
    apply Fin.ext
    exact (Nat.add_assoc _ _ _).symm
  simp only [retainedWires, Equiv.trans_apply, regroup,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.refl_apply, finSumFinEquiv_apply_right]

/-- The original source and its whole complement retain the same physical positions beside Extra. -/
def retainRight (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (extra : BinaryLabelEncoding Extra) :
    FullPlacement (BinaryLabelEncoding.prod source (BinaryLabelEncoding.prod saved extra))
      (BinaryLabelEncoding.prod target extra) :=
  ofGrouping _ _
    ((Equiv.prodCongr whole.grouping (Equiv.refl Extra)).trans (Equiv.prodAssoc Source Saved Extra))
    (whole.retainedWires extra.width) (by
      intro state index
      change (BinaryBasis.bigEndianEquiv (target.width + extra.width)).symm
        (prodEquiv (target.encode state.1, extra.encode state.2))
        (whole.retainedWires extra.width index) =
          (BinaryBasis.bigEndianEquiv (source.width + (saved.width + extra.width))).symm
            (prodEquiv (source.encode (whole.grouping state.1).1,
              prodEquiv (saved.encode (whole.grouping state.1).2, extra.encode state.2))) index
      refine Fin.addCases (m := source.width) (n := saved.width + extra.width)
        (fun primary => ?_) (fun suffix => ?_) index
      · rw [whole.retainedWires_source]
        rw [BinaryBasis.bigEndianEquiv_prod_left]
        rw [BinaryBasis.bigEndianEquiv_prod_left, ← whole.basis_encode state.1]
        have original := whole.basis_position
          ((BinaryLabelEncoding.prod source saved).encode (whole.grouping state.1))
          (Fin.castAdd saved.width primary)
        exact original.trans (BinaryBasis.bigEndianEquiv_prod_left _ _ primary)
      · refine Fin.addCases (m := saved.width) (n := extra.width)
          (fun secondary => ?_) (fun retained => ?_) suffix
        · rw [whole.retainedWires_saved]
          rw [BinaryBasis.bigEndianEquiv_prod_left]
          rw [BinaryBasis.bigEndianEquiv_prod_right, BinaryBasis.bigEndianEquiv_prod_left,
            ← whole.basis_encode state.1]
          have original := whole.basis_position
            ((BinaryLabelEncoding.prod source saved).encode (whole.grouping state.1))
            (Fin.natAdd source.width secondary)
          exact original.trans (BinaryBasis.bigEndianEquiv_prod_right _ _ secondary)
        · rw [whole.retainedWires_extra]
          rw [BinaryBasis.bigEndianEquiv_prod_right]
          rw [BinaryBasis.bigEndianEquiv_prod_right, BinaryBasis.bigEndianEquiv_prod_right])

/-- The complete appended frame restores exactly the same existing suffix state. -/
lemma retainRight_step (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (extra : BinaryLabelEncoding Extra) (action : Source → Source) (state : Target × Extra) :
    (whole.retainRight extra).step (fun pair => (action pair.1, pair.2)) state =
      (whole.step (fun pair => (action pair.1, pair.2)) state.1, state.2) := rfl

/-- The selected prefix remains at the same original positions before the retained suffix. -/
lemma retainRight_mappedWire_source
    (whole : FullPlacement (BinaryLabelEncoding.prod source saved) target)
    (extra : BinaryLabelEncoding Extra) (index : Fin source.width) :
    (whole.retainRight extra).mappedWire (Fin.castAdd (saved.width + extra.width) index) =
      Fin.castAdd extra.width (whole.mappedWire (Fin.castAdd saved.width index)) := by
  have position : (whole.retainRight extra).mappedWire
      (Fin.castAdd (saved.width + extra.width) index) =
        whole.retainedWires extra.width
          (Fin.castAdd (saved.width + extra.width) index) := by
    apply Fin.ext
    change wireAddress (BinaryLabelEncoding.prod source (BinaryLabelEncoding.prod saved extra))
      (BinaryLabelEncoding.prod target extra) (whole.retainedWires extra.width)
      (Fin.castAdd (saved.width + extra.width) index).val = _
    exact dif_pos (Fin.isLt _)
  exact position.trans (whole.retainedWires_source extra.width index)

end

end QuantumAlg.EncodedBit.FullPlacement
