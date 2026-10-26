/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Segments

/-!
# The same source replacement in the original and contiguous coordinates

The actual selected-source partition and the symbolic before/current/later
partition replace precisely the same original bits. Their complements use
different carriers, but every unselected bit remains identical. The resulting
feed is the same mathematical operator on the same full source and reference.
No physical permutation or additional register is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

private lemma segmentPartition_symm (beforeWidth active later : Nat)
    (current : (Qubits active).Index) (before : (Qubits beforeWidth).Index)
    (after : (Qubits later).Index) :
    (segmentPartition beforeWidth active later).symm (current, (before, after)) =
      prodEquiv (before, prodEquiv (current, after)) := by
  apply (segmentPartition beforeWidth active later).injective
  rw [Equiv.apply_symm_apply, window_source_segmentPartition_prod]

/-- Replacing the current contiguous block preserves the actual complete source complement. -/
lemma window_source_segmentReplacement_saved (beforeWidth active later : Nat)
    (label : (Qubits (beforeWidth + (active + later))).Index)
    (current : (Qubits active).Index) :
    (labelPartition (segmentPositions beforeWidth active later)
      ((segmentPartition beforeWidth active later).symm
        (current, (segmentPartition beforeWidth active later label).2))).2 =
      (labelPartition (segmentPositions beforeWidth active later) label).2 := by
  apply (window_sourcePartition_remainder_eq_iff
    (segmentPositions beforeWidth active later) _ label).mpr
  intro index
  let split := segmentPartition beforeWidth active later label
  have original : label = prodEquiv (split.2.1, prodEquiv (split.1, split.2.2)) := by
    exact ((segmentPartition beforeWidth active later).symm_apply_apply label).symm.trans
      (segmentPartition_symm beforeWidth active later split.1 split.2.1 split.2.2)
  have replacement :
      (segmentPartition beforeWidth active later).symm
          (current, (segmentPartition beforeWidth active later label).2) =
        prodEquiv (split.2.1, prodEquiv (current, split.2.2)) :=
    segmentPartition_symm beforeWidth active later current split.2.1 split.2.2
  by_cases before : index.val.val < beforeWidth
  · let position : Fin beforeWidth := ⟨index.val.val, before⟩
    have same : index.val = Fin.castAdd (active + later) position := Fin.ext rfl
    rw [same, replacement, original,
      BinaryBasis.bigEndianEquiv_prod_left, BinaryBasis.bigEndianEquiv_prod_left]
  · have after : beforeWidth + active ≤ index.val.val := by
      by_contra notAfter
      have activeBound : index.val.val - beforeWidth < active := by omega
      let position : Fin active := ⟨index.val.val - beforeWidth, activeBound⟩
      have same : index.val = segmentPositions beforeWidth active later position := by
        apply Fin.ext
        change index.val.val = beforeWidth + (index.val.val - beforeWidth)
        omega
      have selected : index.val ∈
          (labelEmbedding (segmentPositions beforeWidth active later)).selection := by
        rw [same]
        exact Finset.mem_map_of_mem _ (Finset.mem_univ position)
      exact (Finset.mem_compl.mp index.property) selected
    let position : Fin later := ⟨index.val.val - (beforeWidth + active), by
      have bound := index.val.isLt
      omega⟩
    have same : index.val = Fin.natAdd beforeWidth (Fin.natAdd active position) := by
      apply Fin.ext
      change index.val.val = beforeWidth + (active + (index.val.val - (beforeWidth + active)))
      omega
    rw [same, replacement, original,
      BinaryBasis.bigEndianEquiv_prod_right, BinaryBasis.bigEndianEquiv_prod_right,
      BinaryBasis.bigEndianEquiv_prod_right, BinaryBasis.bigEndianEquiv_prod_right]

/-- The original selected partition replaces exactly the same current source bits. -/
lemma window_sourcePartition_segment_replace (beforeWidth active later : Nat)
    (label : (Qubits (beforeWidth + (active + later))).Index)
    (current : (Qubits active).Index) :
    (labelPartition (segmentPositions beforeWidth active later)).symm
        (current, (labelPartition (segmentPositions beforeWidth active later) label).2) =
      (segmentPartition beforeWidth active later).symm
        (current, (segmentPartition beforeWidth active later label).2) := by
  let replacement := (segmentPartition beforeWidth active later).symm
    (current, (segmentPartition beforeWidth active later label).2)
  have selected :
      (labelPartition (segmentPositions beforeWidth active later) replacement).1 = current :=
    (window_sourcePartition_segment_selected beforeWidth active later replacement).trans
      (congrArg Prod.fst ((segmentPartition beforeWidth active later).apply_symm_apply _))
  apply (labelPartition (segmentPositions beforeWidth active later)).injective
  exact ((labelPartition (segmentPositions beforeWidth active later)).apply_symm_apply _).trans
    (Prod.ext selected.symm
      (window_source_segmentReplacement_saved beforeWidth active later label current).symm)

/-- The actual source feed and its contiguous-coordinate form are the same full basis map. -/
lemma window_sourceFeed_segment_basis {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (beforeWidth later : Nat) (Reference : Register)
    (row : (ctx.register.prod
      ((Qubits (beforeWidth + (active + later))).prod Reference)).Index) :
    selectedFeedBasis ports (labelPartition (segmentPositions beforeWidth active later))
        Reference row =
      selectedFeedBasis ports (segmentPartition beforeWidth active later) Reference row := by
  dsimp only [selectedFeedBasis]
  rw [window_sourcePartition_segment_selected, window_sourcePartition_segment_replace]

/-- The original physical-source selection has the same mathematical feed operator. -/
lemma window_sourceFeed_segment_operator {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (beforeWidth later : Nat) (Reference : Register) :
    selectedFeedOperator ports (labelPartition (segmentPositions beforeWidth active later))
        Reference =
      selectedFeedOperator ports (segmentPartition beforeWidth active later) Reference := by
  unfold selectedFeedOperator
  congr 1
  apply Equiv.ext
  exact window_sourceFeed_segment_basis ports beforeWidth later Reference

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
