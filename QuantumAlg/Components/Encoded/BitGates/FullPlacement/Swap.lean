/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Append
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Static complete coordinates for the two original product blocks

The semantic grouping and original physical addresses are swapped together.
This constructs a placement certificate, without executing a data permutation.
An actual program placed through it retains all native instructions.
-/

namespace QuantumAlg.EncodedBit.FullPlacement

noncomputable section

private def swapBlockWires (leftWidth rightWidth : Nat) :
    Fin (leftWidth + rightWidth) ≃ Fin (rightWidth + leftWidth) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumComm (Fin leftWidth) (Fin rightWidth)).trans finSumFinEquiv)

private lemma swapBlockWires_left (leftWidth rightWidth : Nat) (index : Fin leftWidth) :
    swapBlockWires leftWidth rightWidth (Fin.castAdd rightWidth index) =
      Fin.natAdd rightWidth index := by
  simp only [swapBlockWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd]
  rfl

private lemma swapBlockWires_right (leftWidth rightWidth : Nat) (index : Fin rightWidth) :
    swapBlockWires leftWidth rightWidth (Fin.natAdd leftWidth index) =
      Fin.castAdd leftWidth index := by
  simp only [swapBlockWires, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd]
  rfl

variable {Left Right : Type} (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)

/-- View the same two original blocks with their static source and target roles interchanged. -/
def prodSwap : FullPlacement (BinaryLabelEncoding.prod left right)
    (BinaryLabelEncoding.prod right left) :=
  ofGrouping _ _ (Equiv.prodComm Right Left) (swapBlockWires left.width right.width) (by
    intro state index
    change
      (BinaryBasis.bigEndianEquiv (right.width + left.width)).symm
        (prodEquiv (right.encode state.1, left.encode state.2))
        (swapBlockWires left.width right.width index) =
      (BinaryBasis.bigEndianEquiv (left.width + right.width)).symm
        (prodEquiv (left.encode state.2, right.encode state.1)) index
    refine Fin.addCases (m := left.width) (n := right.width)
      (fun first => ?_) (fun last => ?_) index
    · rw [swapBlockWires_left, BinaryBasis.bigEndianEquiv_prod_right,
        BinaryBasis.bigEndianEquiv_prod_left]
    · rw [swapBlockWires_right, BinaryBasis.bigEndianEquiv_prod_left,
        BinaryBasis.bigEndianEquiv_prod_right])

lemma prodSwap_grouping : (prodSwap left right).grouping = Equiv.prodComm Right Left := rfl

/-- Every source-left wire is the corresponding original target-right wire. -/
lemma prodSwap_mappedWire_left (index : Fin left.width) :
    (prodSwap left right).mappedWire (Fin.castAdd right.width index) =
      Fin.natAdd right.width index := by
  have actual : (prodSwap left right).mappedWire (Fin.castAdd right.width index) =
      swapBlockWires left.width right.width (Fin.castAdd right.width index) := by
    apply Fin.ext
    change wireAddress (BinaryLabelEncoding.prod left right)
      (BinaryLabelEncoding.prod right left) (swapBlockWires left.width right.width)
        (Fin.castAdd right.width index).val = _
    exact dif_pos (Fin.castAdd right.width index).isLt
  exact actual.trans (swapBlockWires_left _ _ index)

/-- Every source-right wire is the corresponding original target-left wire. -/
lemma prodSwap_mappedWire_right (index : Fin right.width) :
    (prodSwap left right).mappedWire (Fin.natAdd left.width index) =
      Fin.castAdd left.width index := by
  have actual : (prodSwap left right).mappedWire (Fin.natAdd left.width index) =
      swapBlockWires left.width right.width (Fin.natAdd left.width index) := by
    apply Fin.ext
    change wireAddress (BinaryLabelEncoding.prod left right)
      (BinaryLabelEncoding.prod right left) (swapBlockWires left.width right.width)
        (Fin.natAdd left.width index).val = _
    exact dif_pos (Fin.natAdd left.width index).isLt
  exact actual.trans (swapBlockWires_right _ _ index)

/-- The entire static grouping transports the full supplied action on both original blocks. -/
lemma prodSwap_step (action : Left × Right → Left × Right) (state : Right × Left) :
    (prodSwap left right).step action state =
      ((action (state.2, state.1)).2, (action (state.2, state.1)).1) := rfl

end

end QuantumAlg.EncodedBit.FullPlacement
