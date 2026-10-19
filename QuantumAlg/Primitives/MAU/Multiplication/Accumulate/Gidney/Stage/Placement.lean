/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.SourceLayout
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Physical placement of the borrowed-bit accumulation stage

Move the trailing helper to the source-word suffix, then permute the source
selector. The semantic grouping and every native gate use precisely these
same wire maps on the original two words.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open BinaryBasis

private lemma decoded_equal {leftWidth rightWidth : Nat}
    (widths : leftWidth = rightWidth)
    (left : Fin (2 ^ leftWidth)) (right : Fin (2 ^ rightWidth)) (labels : left.val = right.val)
    (first : Fin leftWidth) (second : Fin rightWidth) (positions : first.val = second.val) :
    (bigEndianEquiv leftWidth).symm left first =
      (bigEndianEquiv rightWidth).symm right second := by
  have reversed : first.rev.val = second.rev.val := by
    simp only [Fin.val_rev]
    omega
  simp only [bigEndianEquiv_symm_value, labels, reversed]

private def prefixLabel (extra : Nat) (state : CanonicalRegisters extra) : Fin (2 ^ (extra + 2)) :=
  Fin.cast (congrArg (fun width => 2 ^ width) (by omega : 1 + (extra + 1) = extra + 2))
    (prodEquiv (BinaryLabelEncoding.bool.encode state.1,
      prodEquiv (state.2.1, BinaryLabelEncoding.bool.encode state.2.2.1)))

private lemma canonicalGrouped_value (extra : Nat) (state : CanonicalRegisters extra) :
    ((canonicalEncoding extra).encode state).val =
      (prodEquiv (prefixLabel extra state,
        prodEquiv (state.2.2.2.1, BinaryLabelEncoding.bool.encode state.2.2.2.2))).val := by
  change
    ((BinaryLabelEncoding.bool.encode state.2.2.2.2).val +
      2 ^ 1 * state.2.2.2.1.val) +
      2 ^ ((extra + 3) + 1) * (BinaryLabelEncoding.bool.encode state.2.2.1).val +
      2 ^ (1 + ((extra + 3) + 1)) * state.2.1.val +
      2 ^ (extra + (1 + ((extra + 3) + 1))) *
        (BinaryLabelEncoding.bool.encode state.1).val =
    ((BinaryLabelEncoding.bool.encode state.2.2.2.2).val + 2 ^ 1 * state.2.2.2.1.val) +
      2 ^ ((extra + 3) + 1) *
        ((BinaryLabelEncoding.bool.encode state.2.2.1).val + 2 ^ 1 * state.2.1.val +
          2 ^ (extra + 1) * (BinaryLabelEncoding.bool.encode state.1).val)
  simp only [pow_add, pow_one]
  ring

private lemma boolLabel (value : Bool) :
    finTwoEquiv.symm value = (BinaryLabelEncoding.bool.encode value : Fin (2 ^ 1)) := by
  cases value <;> rfl

private lemma sourceGrouped_value (extra : Nat) (state : CanonicalRegisters extra) :
    (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1).val =
      (prodEquiv (prefixLabel extra state,
        BinaryLabelEncoding.bool.encode state.2.2.2.2)).val := by
  change
    (finTwoEquiv.symm state.2.2.2.2).val +
        2 ^ 1 * (finTwoEquiv.symm state.2.2.1).val +
        2 ^ (1 + 1) * state.2.1.val +
        2 ^ (extra + (1 + 1)) * (finTwoEquiv.symm state.1).val =
      (BinaryLabelEncoding.bool.encode state.2.2.2.2).val + 2 ^ 1 *
        ((BinaryLabelEncoding.bool.encode state.2.2.1).val + 2 ^ 1 * state.2.1.val +
          2 ^ (extra + 1) * (BinaryLabelEncoding.bool.encode state.1).val)
  rw [boolLabel, boolLabel, boolLabel]
  simp only [pow_add, pow_one]
  ring

private def packedPosition (extra : Nat) (index : Fin (canonicalEncoding extra).width) :
    Fin (encoding (extra + 3)).width :=
  ⟨packHelperWire extra index.val, by
    have inside : index.val < 2 * (extra + 3) := by
      simpa only [gidneyCanonicalStage_qubit_count] using index.isLt
    change packHelperWire extra index.val < (extra + 3) + (extra + 3)
    unfold packHelperWire
    split_ifs <;> omega⟩

private lemma packed_coordinates (extra : Nat) (state : CanonicalRegisters extra)
    (index : Fin (canonicalEncoding extra).width) :
    (bigEndianEquiv (encoding (extra + 3)).width).symm
        ((encoding (extra + 3)).encode
          (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1, state.2.2.2.1))
        (packedPosition extra index) =
      (bigEndianEquiv (canonicalEncoding extra).width).symm
        ((canonicalEncoding extra).encode state) index := by
  let prefixWord := prefixLabel extra state
  let target := state.2.2.2.1
  let helper : Fin (2 ^ 1) := BinaryLabelEncoding.bool.encode state.2.2.2.2
  let before := prodEquiv (prefixWord, prodEquiv (target, helper))
  let after := prodEquiv (prodEquiv (prefixWord, helper), target)
  let sourceIndex : Fin ((extra + 2) + ((extra + 3) + 1)) :=
    ⟨index.val, by
      have bound := index.isLt
      change index.val < 1 + (extra + (1 + ((extra + 3) + 1))) at bound
      omega⟩
  let targetIndex : Fin (((extra + 2) + 1) + (extra + 3)) :=
    ⟨(packedPosition extra index).val, by
      have bound := (packedPosition extra index).isLt
      change (packedPosition extra index).val < (extra + 3) + (extra + 3) at bound
      omega⟩
  have sourceSame := decoded_equal
    (by change 1 + (extra + (1 + ((extra + 3) + 1))) = _; omega)
    ((canonicalEncoding extra).encode state) before (canonicalGrouped_value extra state)
    index sourceIndex rfl
  have targetValues :
      ((encoding (extra + 3)).encode
        (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1, state.2.2.2.1)).val =
      after.val := by
    change target.val + 2 ^ (extra + 3) *
      (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1).val = _
    rw [sourceGrouped_value]
    rfl
  have targetSame := decoded_equal (by change (extra + 3) + (extra + 3) = _; omega)
    ((encoding (extra + 3)).encode
      (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1, state.2.2.2.1))
    after targetValues (packedPosition extra index) targetIndex rfl
  rw [targetSame, sourceSame]
  by_cases prefixPart : index.val < extra + 2
  · let position : Fin (extra + 2) := ⟨index.val, prefixPart⟩
    have sourcePosition : sourceIndex = Fin.castAdd ((extra + 3) + 1) position := rfl
    have targetPosition : targetIndex =
        Fin.castAdd (extra + 3) (Fin.castAdd 1 position) := by
      apply Fin.ext
      simp [targetIndex, packedPosition, packHelperWire, prefixPart, position]
    rw [sourcePosition, targetPosition]
    exact ((bigEndianEquiv_prod_left (prodEquiv (prefixWord, helper)) target
      (Fin.castAdd 1 position)).trans (bigEndianEquiv_prod_left prefixWord helper position)).trans
        (bigEndianEquiv_prod_left prefixWord (prodEquiv (target, helper)) position).symm
  · by_cases targetPart : index.val < extra + 2 + (extra + 3)
    · let position : Fin (extra + 3) := ⟨index.val - (extra + 2), by omega⟩
      have sourcePosition : sourceIndex = Fin.natAdd (extra + 2) (Fin.castAdd 1 position) := by
        apply Fin.ext
        change index.val = extra + 2 + (index.val - (extra + 2))
        omega
      have targetPosition : targetIndex = Fin.natAdd ((extra + 2) + 1) position := by
        apply Fin.ext
        simp only [targetIndex, packedPosition, packHelperWire,
          if_neg prefixPart, if_pos targetPart, Fin.val_natAdd, position]
        omega
      rw [sourcePosition, targetPosition]
      exact (bigEndianEquiv_prod_right (prodEquiv (prefixWord, helper)) target position).trans
        ((bigEndianEquiv_prod_right prefixWord (prodEquiv (target, helper))
          (Fin.castAdd 1 position)).trans (bigEndianEquiv_prod_left target helper position)).symm
    · have last : index.val = extra + 2 + (extra + 3) := by
        have bound := sourceIndex.isLt
        change index.val < (extra + 2) + ((extra + 3) + 1) at bound
        omega
      have sourcePosition : sourceIndex =
          Fin.natAdd (extra + 2) (Fin.natAdd (extra + 3) (0 : Fin 1)) := by
        apply Fin.ext
        simpa only [Fin.val_natAdd, Fin.val_zero, Nat.add_zero] using last
      have targetPosition : targetIndex =
          Fin.castAdd (extra + 3) (Fin.natAdd (extra + 2) (0 : Fin 1)) := by
        apply Fin.ext
        simp [targetIndex, packedPosition, packHelperWire, last]
      rw [sourcePosition, targetPosition]
      exact ((bigEndianEquiv_prod_left (prodEquiv (prefixWord, helper)) target
        (Fin.natAdd (extra + 2) (0 : Fin 1))).trans
          (bigEndianEquiv_prod_right prefixWord helper (0 : Fin 1))).trans
        ((bigEndianEquiv_prod_right prefixWord (prodEquiv (target, helper))
          (Fin.natAdd (extra + 3) (0 : Fin 1))).trans
            (bigEndianEquiv_prod_right target helper (0 : Fin 1))).symm

private def prefixPermutationPosition {width : Nat} (permutation : Equiv.Perm (Fin width))
    (index : Fin (width + width)) : Fin (width + width) :=
  ⟨extendWirePermutation permutation index.val, by
    by_cases inside : index.val < width
    · have bound := binaryExtendWirePermutation_range permutation index.val inside
      omega
    · rw [binaryExtendWirePermutation_outside permutation index.val (by omega)]
      exact index.isLt⟩

private lemma prefixPermutation_coordinates {width : Nat}
    (permutation : Equiv.Perm (Fin width)) (source target : Fin (2 ^ width))
    (index : Fin (width + width)) :
    (bigEndianEquiv (width + width)).symm
        (prodEquiv (permuteLabel permutation source, target))
        (prefixPermutationPosition permutation index) =
      (bigEndianEquiv (width + width)).symm (prodEquiv (source, target)) index := by
  by_cases first : index.val < width
  · let position : Fin width := ⟨index.val, first⟩
    have original : index = Fin.castAdd width position := rfl
    have moved : prefixPermutationPosition permutation index =
        Fin.castAdd width (permutation position) := by
      apply Fin.ext
      exact binaryExtendWirePermutation_apply permutation position
    rw [moved, original]
    have read : (bigEndianEquiv width).symm (permuteLabel permutation source)
        (permutation position) = (bigEndianEquiv width).symm source position := by
      simp only [bigEndianEquiv_symm_value, binaryPermuteLabel_bit]
    exact ((bigEndianEquiv_prod_left (permuteLabel permutation source) target
      (permutation position)).trans read).trans
        (bigEndianEquiv_prod_left source target position).symm
  · let position : Fin width := ⟨index.val - width, by have := index.isLt; omega⟩
    have original : index = Fin.natAdd width position := by
      apply Fin.ext
      change index.val = width + (index.val - width)
      omega
    have moved : prefixPermutationPosition permutation index = Fin.natAdd width position := by
      apply Fin.ext
      change extendWirePermutation permutation index.val = width + (index.val - width)
      rw [binaryExtendWirePermutation_outside permutation index.val (by omega)]
      omega
    rw [moved, original]
    exact (bigEndianEquiv_prod_right (permuteLabel permutation source) target position).trans
      (bigEndianEquiv_prod_right source target position).symm

private def stagePosition (extra : Nat) (selected : Fin (extra + 3)) :
    Fin (canonicalEncoding extra).width ↪ Fin (encoding (extra + 3)).width where
  toFun index := ⟨stagePlacementWire extra selected index.val, by
    have inside : index.val < 2 * (extra + 3) := by
      simpa only [gidneyCanonicalStage_qubit_count] using index.isLt
    have bound := gidneyStagePlacementWire_range extra selected index.val inside
    change stagePlacementWire extra selected index.val < (extra + 3) + (extra + 3)
    omega⟩
  inj' := by
    intro first second same
    exact Fin.ext (gidneyStagePlacementWire_injective extra selected (congrArg Fin.val same))

private lemma selected_coordinates (extra : Nat) (selected : Fin (extra + 3))
    (state : CanonicalRegisters extra) (index : Fin (canonicalEncoding extra).width) :
    (bigEndianEquiv (encoding (extra + 3)).width).symm
        ((encoding (extra + 3)).encode (selectedWordsEquiv extra selected state))
        (stagePosition extra selected index) =
      (bigEndianEquiv (canonicalEncoding extra).width).symm
        ((canonicalEncoding extra).encode state) index :=
  (prefixPermutation_coordinates (selectorPermutation extra selected)
    (sourceLabelEquiv extra (canonicalFieldsEquiv extra state).1) state.2.2.2.1
    (packedPosition extra index)).trans (packed_coordinates extra state index)

private lemma stagePosition_surjective (extra : Nat) (selected : Fin (extra + 3)) :
    Function.Surjective (stagePosition extra selected) := by
  have sameWidth : (canonicalEncoding extra).width = (encoding (extra + 3)).width := by
    rw [gidneyCanonicalStage_qubit_count]
    change 2 * (extra + 3) = (extra + 3) + (extra + 3)
    omega
  let endomap := fun index : Fin (canonicalEncoding extra).width =>
    Fin.cast sameWidth.symm (stagePosition extra selected index)
  have injective : Function.Injective endomap := by
    intro first second same
    have values := congrArg (fun index : Fin (canonicalEncoding extra).width => index.val) same
    exact (stagePosition extra selected).injective (Fin.ext values)
  intro target
  obtain ⟨source, same⟩ := Finite.surjective_of_injective injective (Fin.cast sameWidth.symm target)
  have values := congrArg (fun index : Fin (canonicalEncoding extra).width => index.val) same
  exact ⟨source, Fin.ext values⟩

/-- One certified placement ties the semantic grouping to the actual helper and selector wires. -/
def stageFullPlacement (extra : Nat) (selected : Fin (extra + 3)) :
    EncodedBit.FullPlacement (canonicalEncoding extra) (encoding (extra + 3)) where
  grouping := (selectedWordsEquiv extra selected).symm
  basis := stagePlacementIndex extra selected
  basis_encode := by
    intro state
    exact (gidneyStagePlacementIndex_encode extra selected
      ((selectedWordsEquiv extra selected).symm state)).trans
        (congrArg (encoding (extra + 3)).encode
          ((selectedWordsEquiv extra selected).apply_symm_apply state))
  physicalIndex := stagePlacementWire extra selected
  wire_injective := by
    intro first second same
    exact Fin.ext (gidneyStagePlacementWire_injective extra selected same)
  wire_within index := (stagePosition extra selected index).isLt
  wire_surjective := stagePosition_surjective extra selected
  basis_position := by
    intro label index
    obtain ⟨state, rfl⟩ := (canonicalLabelEquiv extra).surjective label
    rw [gidneyCanonicalLabel_encode, gidneyStagePlacementIndex_encode]
    exact selected_coordinates extra selected state index

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
