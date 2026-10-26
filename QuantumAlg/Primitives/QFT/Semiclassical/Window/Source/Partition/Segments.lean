/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments

/-!
# Original selected bits and contiguous source segments

The physical-source selection already used by the actual sampler reads the
same contiguous mathematical block as the integer product coordinates.
Its complete complement is characterized pointwise, retaining every other
source bit. No readout cell or measured-frequency convention is changed.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

/-- Literal original contiguous positions, after the consumed prefix and before the suffix. -/
def segmentPositions (beforeWidth active later : Nat) :
    Fin active ↪ Fin (beforeWidth + (active + later)) where
  toFun index := Fin.natAdd beforeWidth (Fin.castAdd later index)
  inj' := by
    intro left right equal
    apply Fin.ext
    have values := congrArg Fin.val equal
    change beforeWidth + left.val = beforeWidth + right.val at values
    omega

/-- The actual source-selector block is exactly the same original contiguous integer block. -/
lemma window_sourcePartition_segment_selected (beforeWidth active later : Nat)
    (label : (Qubits (beforeWidth + (active + later))).Index) :
    (labelPartition (segmentPositions beforeWidth active later) label).1 =
      (segmentPartition beforeWidth active later label).1 := by
  apply (BinaryBasis.bigEndianEquiv active).symm.injective
  funext index
  rw [window_sourcePartition_coordinate, window_source_segmentPartition_coordinate,
    BinaryBasis.bigEndianEquiv_symm_value]
  rfl

/-- Equality of complete saved source coordinates is precisely equality at every unselected bit. -/
lemma window_sourcePartition_remainder_eq_iff {full active : Nat}
    (positions : Fin active ↪ Fin full) (left right : (Qubits full).Index) :
    (labelPartition positions left).2 = (labelPartition positions right).2 ↔
      ∀ index : QuantumLayout.SelectedPosition (labelEmbedding positions).selectionᶜ,
        (BinaryBasis.bigEndianEquiv full).symm left index.val =
          (BinaryBasis.bigEndianEquiv full).symm right index.val := by
  change ((labelEmbedding positions).splitBasis
      ((BinaryBasis.bigEndianEquiv full).symm left)).2 =
    ((labelEmbedding positions).splitBasis
      ((BinaryBasis.bigEndianEquiv full).symm right)).2 ↔ _
  constructor
  · intro equal index
    exact congrFun equal index
  · intro equal
    funext index
    exact equal index

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
