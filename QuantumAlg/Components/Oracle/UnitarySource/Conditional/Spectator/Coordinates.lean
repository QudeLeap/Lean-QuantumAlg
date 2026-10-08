/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.UnitarySource.Conditional.Spectator
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Original selector and source coordinates around the spectator

The local query arguments consist of the original selector followed by the
original source bits. The intervening phase bit is not a query argument.
-/

namespace QuantumAlg.UnitarySource.Conditional
noncomputable section

/-- Original selector, intervening phase and complete source in physical binary order. -/
def spectatorBasis {width : Nat} (selector phase : Fin 2) (source : Fin (2 ^ width)) :
    (layout (1 + width)).Basis :=
  (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm
    (prodEquiv (selector, prodEquiv (phase, source)))

private theorem position_zero (width : Nat) :
    spectatorPositions width (0 : Fin (1 + width)) = 0 := by
  apply Fin.ext
  simp [spectatorPositions]

private theorem position_right {width : Nat} (index : Fin width) :
    spectatorPositions width (Fin.natAdd 1 index) = Fin.natAdd 1 (Fin.natAdd 1 index) := by
  apply Fin.ext
  change (if 1 + index.val = 0 then 0 else 1 + (1 + index.val)) = 1 + (1 + index.val)
  rw [if_neg (by omega)]

/-- Exact local query arguments, independent of the intervening phase value. -/
theorem spectator_selected_basis {width : Nat} (selector phase : Fin 2)
    (source : Fin (2 ^ width)) :
    UnitaryCircuit.selectedInput (layout width) (layout (1 + width))
      (spectatorPositions width) (fun _ => rfl) (spectatorBasis selector phase source) =
      (QuantumSignature.qubitsIndexEquiv (1 + width)).symm (prodEquiv (selector, source)) := by
  funext index
  apply Fin.ext
  change (spectatorBasis selector phase source (spectatorPositions width index)).val = _
  refine Fin.addCases (fun first => ?_) (fun index => ?_) index
  · have zero : first = 0 := Subsingleton.elim _ _
    subst first
    change (spectatorBasis selector phase source
      (spectatorPositions width (0 : Fin (1 + width)))).val = _
    rw [position_zero]
    exact (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := 1) (rightWidth := 1 + width) selector (prodEquiv (phase, source)) 0)).trans
      (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
        (leftWidth := 1) (rightWidth := width) selector source 0)).symm
  · rw [position_right]
    have outer := BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := 1) (rightWidth := 1 + width) selector (prodEquiv (phase, source))
      (Fin.natAdd 1 index)
    have inner := BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := 1) (rightWidth := width) phase source index
    have localSource := BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := 1) (rightWidth := width) selector source index
    exact (congrArg Fin.val (outer.trans inner)).trans (congrArg Fin.val localSource).symm

/-- The phase coordinate is not among the query arguments, including an empty source suffix. -/
theorem spectator_not_selected (width : Nat) :
    (⟨1, by omega⟩ : Fin (1 + (1 + width))) ∉
      Finset.univ.map (spectatorPositions width) := by
  intro member
  obtain ⟨index, _, same⟩ := Finset.mem_map.mp member
  have values := congrArg Fin.val same
  change (if index.val = 0 then 0 else 1 + index.val) = 1 at values
  split_ifs at values
  omega

/-- Every untouched coordinate is precisely the original phase wire. -/
theorem spectator_only_complement (width : Nat) (index : Fin (1 + (1 + width)))
    (outside : index ∉ Finset.univ.map (spectatorPositions width)) : index.val = 1 := by
  by_contra different
  apply outside
  by_cases zero : index.val = 0
  · refine Finset.mem_map.mpr ⟨0, Finset.mem_univ _, ?_⟩
    rw [position_zero]
    exact Fin.ext zero.symm
  · let localIndex : Fin (1 + width) := ⟨index.val - 1, by omega⟩
    refine Finset.mem_map.mpr ⟨localIndex, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (if localIndex.val = 0 then 0 else 1 + localIndex.val) = index.val
    have positive : localIndex.val ≠ 0 := by dsimp [localIndex]; omega
    rw [if_neg positive]
    dsimp [localIndex]
    omega

end
end QuantumAlg.UnitarySource.Conditional
