/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Swap

/-!
# Complete coordinates for a source, two supplied controls and a retained word

The source and arbitrary retained word keep their original physical
positions. The two flags selected by a subroutine are the first and last
of three actual suffix bits. The middle suffix bit is retained with the
word. This certificate places each real instruction at those positions;
it neither executes a swap nor assumes any of the flags is clean.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

namespace Interleave

variable {Data Saved : Type} (data : BinaryLabelEncoding Data)
    (saved : BinaryLabelEncoding Saved)

abbrev flags := BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

abbrev suffix := BinaryLabelEncoding.prod BinaryLabelEncoding.bool flags

abbrev source := BinaryLabelEncoding.prod (BinaryLabelEncoding.prod data flags)
  (BinaryLabelEncoding.prod saved BinaryLabelEncoding.bool)

abbrev target := BinaryLabelEncoding.prod (BinaryLabelEncoding.prod data saved) suffix

/-- Preserve both complete words, select the two actual outer suffix positions, and retain N. -/
def grouping : ((Data × Saved) × (Bool × (Bool × Bool))) ≃
    ((Data × (Bool × Bool)) × (Saved × Bool)) where
  toFun state := ((state.1.1, (state.2.1, state.2.2.2)), (state.1.2, state.2.2.1))
  invFun state := ((state.1.1, state.2.1), (state.1.2.1, (state.2.2, state.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

private def sourceParts (first last : Nat) :
    Fin ((first + (1 + 1)) + (last + 1)) ≃
      ((Fin first ⊕ (Fin 1 ⊕ Fin 1)) ⊕ (Fin last ⊕ Fin 1)) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm))
      finSumFinEquiv.symm)

private def targetParts (first last : Nat) :
    Fin ((first + last) + (1 + (1 + 1))) ≃
      ((Fin first ⊕ Fin last) ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Fin 1))) :=
  finSumFinEquiv.symm.trans
    (Equiv.sumCongr finSumFinEquiv.symm
      (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm)))

private def reorderParts (first last : Nat) :
    ((Fin first ⊕ (Fin 1 ⊕ Fin 1)) ⊕ (Fin last ⊕ Fin 1)) ≃
      ((Fin first ⊕ Fin last) ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Fin 1))) where
  toFun
    | .inl (.inl index) => .inl (.inl index)
    | .inl (.inr (.inl index)) => .inr (.inl index)
    | .inl (.inr (.inr index)) => .inr (.inr (.inr index))
    | .inr (.inl index) => .inl (.inr index)
    | .inr (.inr index) => .inr (.inr (.inl index))
  invFun
    | .inl (.inl index) => .inl (.inl index)
    | .inl (.inr index) => .inr (.inl index)
    | .inr (.inl index) => .inl (.inr (.inl index))
    | .inr (.inr (.inl index)) => .inr (.inr index)
    | .inr (.inr (.inr index)) => .inl (.inr (.inr index))
  left_inv := by rintro ((index | (index | index)) | (index | index)) <;> rfl
  right_inv := by rintro ((index | index) | (index | (index | index))) <;> rfl

private def wires (first last : Nat) :
    Fin ((first + (1 + 1)) + (last + 1)) ≃ Fin ((first + last) + (1 + (1 + 1))) :=
  (sourceParts first last).trans
    ((reorderParts first last).trans (targetParts first last).symm)

private lemma wires_eq (first last : Nat)
    (input : Fin ((first + (1 + 1)) + (last + 1)))
    (output : Fin ((first + last) + (1 + (1 + 1))))
    (same : reorderParts first last (sourceParts first last input) =
      targetParts first last output) :
    wires first last input = output := by
  apply (targetParts first last).injective
  change (targetParts first last) ((targetParts first last).symm
    (reorderParts first last (sourceParts first last input))) = _
  rw [Equiv.apply_symm_apply]
  exact same

private lemma wires_data (first last : Nat) (index : Fin first) :
    wires first last (Fin.castAdd (last + 1) (Fin.castAdd (1 + 1) index)) =
      Fin.castAdd (1 + (1 + 1)) (Fin.castAdd last index) := by
  apply wires_eq
  simp only [sourceParts, targetParts, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.refl_apply, reorderParts, Equiv.coe_fn_mk]

private lemma wires_control (first last : Nat) (index : Fin 1) :
    wires first last (Fin.castAdd (last + 1) (Fin.natAdd first (Fin.castAdd 1 index))) =
      Fin.natAdd (first + last) (Fin.castAdd (1 + 1) index) := by
  apply wires_eq
  simp only [sourceParts, targetParts, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, Equiv.refl_apply,
    reorderParts, Equiv.coe_fn_mk]

private lemma wires_work (first last : Nat) (index : Fin 1) :
    wires first last (Fin.castAdd (last + 1) (Fin.natAdd first (Fin.natAdd 1 index))) =
      Fin.natAdd (first + last) (Fin.natAdd 1 (Fin.natAdd 1 index)) := by
  apply wires_eq
  simp only [sourceParts, targetParts, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, reorderParts, Equiv.coe_fn_mk]

private lemma wires_saved (first last : Nat) (index : Fin last) :
    wires first last (Fin.natAdd (first + (1 + 1)) (Fin.castAdd 1 index)) =
      Fin.castAdd (1 + (1 + 1)) (Fin.natAdd first index) := by
  apply wires_eq
  simp only [sourceParts, targetParts, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, reorderParts, Equiv.coe_fn_mk]

private lemma wires_middle (first last : Nat) (index : Fin 1) :
    wires first last (Fin.natAdd (first + (1 + 1)) (Fin.natAdd last index)) =
      Fin.natAdd (first + last) (Fin.natAdd 1 (Fin.castAdd 1 index)) := by
  apply wires_eq
  simp only [sourceParts, targetParts, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, reorderParts, Equiv.coe_fn_mk]

/-- Full original words and all three suffix bits occur exactly once in this placement. -/
def placement : FullPlacement (source data saved) (target data saved) :=
  ofGrouping _ _ grouping (wires data.width saved.width) (by
    intro state index
    let firstFlag : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode state.2.1
    let middleFlag : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode state.2.2.1
    let lastFlag : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode state.2.2.2
    change (BinaryBasis.bigEndianEquiv ((data.width + saved.width) + (1 + (1 + 1)))).symm
        (prodEquiv (prodEquiv (data.encode state.1.1, saved.encode state.1.2),
          prodEquiv (firstFlag, prodEquiv (middleFlag, lastFlag))))
        (wires data.width saved.width index) =
      (BinaryBasis.bigEndianEquiv ((data.width + (1 + 1)) + (saved.width + 1))).symm
        (prodEquiv (prodEquiv (data.encode state.1.1,
          prodEquiv (firstFlag, lastFlag)), prodEquiv (saved.encode state.1.2, middleFlag))) index
    refine Fin.addCases (m := data.width + (1 + 1)) (n := saved.width + 1)
      (fun primary => ?_) (fun retained => ?_) index
    · refine Fin.addCases (m := data.width) (n := 1 + 1)
        (fun original => ?_) (fun flag => ?_) primary
      · simp only [wires_data,
          BinaryBasis.bigEndianEquiv_prod_left]
      · refine Fin.addCases (m := 1) (n := 1) (fun control => ?_) (fun work => ?_) flag
        · simp only [wires_control,
            BinaryBasis.bigEndianEquiv_prod_left, BinaryBasis.bigEndianEquiv_prod_right]
        · simp only [wires_work,
            BinaryBasis.bigEndianEquiv_prod_left, BinaryBasis.bigEndianEquiv_prod_right]
    · refine Fin.addCases (m := saved.width) (n := 1)
        (fun word => ?_) (fun middle => ?_) retained
      · simp only [wires_saved,
          BinaryBasis.bigEndianEquiv_prod_left, BinaryBasis.bigEndianEquiv_prod_right]
      · simp only [wires_middle,
          BinaryBasis.bigEndianEquiv_prod_right]
        rw [BinaryBasis.bigEndianEquiv_prod_left (leftWidth := 1) (rightWidth := 1)])

/-- The exact complete grouping, without a valid-state or flag-cleanliness restriction. -/
lemma placement_grouping : (placement data saved).grouping = grouping := rfl

end Interleave

end

end QuantumAlg.EncodedBit.FullPlacement
