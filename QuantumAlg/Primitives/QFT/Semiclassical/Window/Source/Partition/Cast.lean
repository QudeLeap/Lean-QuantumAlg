/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition

/-!
# Width equalities preserve the same selected mathematical source

Transporting an original source position through a proved width equality
changes neither its selected label nor its complete replacement. These are
finite coordinate identities; no physical wire or readout cell is moved.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

/-- Keep every selected original position through a literal width equality. -/
def castPositions {before after active : Nat} (widths : before = after)
    (positions : Fin active ↪ Fin before) : Fin active ↪ Fin after :=
  positions.trans (finCongr widths).toEmbedding

/-- Selected source values are unchanged by a width equality. -/
lemma window_sourcePartition_cast_selected {before after active : Nat}
    (widths : before = after) (positions : Fin active ↪ Fin before)
    (label : (Qubits before).Index) :
    (labelPartition (castPositions widths positions)
      (Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) label)).1 =
      (labelPartition positions label).1 := by
  cases widths
  rfl

/-- Current replacement retains the identical full finite source label. -/
lemma window_sourcePartition_cast_replace {before after active : Nat}
    (widths : before = after) (positions : Fin active ↪ Fin before)
    (label : (Qubits before).Index) (current : (Qubits active).Index) :
    (labelPartition (castPositions widths positions)).symm
        (current, (labelPartition (castPositions widths positions)
          (Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths) label)).2) =
      Fin.cast (congrArg (fun width : Nat => 2 ^ width) widths)
        ((labelPartition positions).symm (current, (labelPartition positions label).2)) := by
  cases widths
  rfl

/-- The same two original source words through a symbolic total-width equality. -/
def pairedLabelEquiv (bits width : Nat) (widths : width = bits + bits) :
    ((Qubits bits).prod (Qubits bits)).Index ≃ (Qubits width).Index :=
  (prodEquiv (m := bits) (n := bits)).trans
    (finCongr (congrArg (fun size : Nat => 2 ^ size) widths).symm)

/-- The symbolic width transport retains the original zero pair. -/
lemma window_sourcePairedLabel_zero (bits width : Nat) (widths : width = bits + bits) :
    pairedLabelEquiv bits width widths (0, 0) = 0 := by
  apply Fin.ext
  change 0 + 2 ^ bits * 0 = 0
  rw [Nat.mul_zero, Nat.zero_add]

/-- Selected current coordinates of the same original pair of source words. -/
def pairedPartition (bits : Nat) {active : Nat}
    (positions : Fin active ↪ Fin (bits + bits)) :
    ((Qubits bits).prod (Qubits bits)).Index ≃
      (Qubits active).Index × (labelRemainder positions).Index :=
  (prodEquiv (m := bits) (n := bits)).trans (labelPartition positions)

private lemma paired_label_cast (bits width : Nat) (widths : width = bits + bits)
    (label : ((Qubits bits).prod (Qubits bits)).Index) :
    (prodEquiv (m := bits) (n := bits)) label =
      Fin.cast (congrArg (fun size : Nat => 2 ^ size) widths)
        (pairedLabelEquiv bits width widths label) := by
  apply Fin.ext
  rfl

/-- Symbolic paired-source selection avoids normalizing any closed exponent width. -/
lemma window_sourcePaired_cast_selected (bits width : Nat) (widths : width = bits + bits)
    {active : Nat} (positions : Fin active ↪ Fin width)
    (label : ((Qubits bits).prod (Qubits bits)).Index) :
    (pairedPartition bits (castPositions widths positions) label).1 =
      (labelPartition positions (pairedLabelEquiv bits width widths label)).1 := by
  change (labelPartition (castPositions widths positions)
    (prodEquiv (m := bits) (n := bits) label)).1 = _
  rw [paired_label_cast, window_sourcePartition_cast_selected]

/-- Symbolic replacement retains both original source words and their complete complement. -/
lemma window_sourcePaired_cast_replace (bits width : Nat) (widths : width = bits + bits)
    {active : Nat} (positions : Fin active ↪ Fin width)
    (label : ((Qubits bits).prod (Qubits bits)).Index) (current : (Qubits active).Index) :
    pairedLabelEquiv bits width widths
        ((pairedPartition bits (castPositions widths positions)).symm
          (current, (pairedPartition bits (castPositions widths positions) label).2)) =
      (labelPartition positions).symm
        (current, (labelPartition positions (pairedLabelEquiv bits width widths label)).2) := by
  apply (finCongr (congrArg (fun size : Nat => 2 ^ size) widths)).injective
  calc
    _ = prodEquiv
        ((pairedPartition bits (castPositions widths positions)).symm
          (current, (pairedPartition bits (castPositions widths positions) label).2)) :=
      (paired_label_cast bits width widths _).symm
    _ = (labelPartition (castPositions widths positions)).symm
        (current, (labelPartition (castPositions widths positions)
          (prodEquiv (m := bits) (n := bits) label)).2) :=
      (prodEquiv (m := bits) (n := bits)).apply_symm_apply _
    _ = _ := by
      rw [paired_label_cast bits width widths label]
      exact window_sourcePartition_cast_replace widths positions
        (pairedLabelEquiv bits width widths label) current

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
