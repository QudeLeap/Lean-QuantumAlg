/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow.Associativity
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Factor

/-!
# The next future preparation on the same mathematical source labels

After the current block is consumed, its identity factor joins the consumed
prefix. Reassociating the symbolic width equality retains every original
finite label. The remaining H tensor is exactly the next future operator on
all columns, including arbitrary consumed prefixes and empty segments.
This is an identity of mathematical source coordinates.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

private lemma combined_identity (before active : Nat)
    (rowFirst columnFirst : (Qubits before).Index)
    (rowCurrent columnCurrent : (Qubits active).Index) :
    (1 : HilbertOperator (Qubits (before + active)))
        (prodEquiv (rowFirst, rowCurrent)) (prodEquiv (columnFirst, columnCurrent)) =
      (1 : HilbertOperator (Qubits before)) rowFirst columnFirst *
        (1 : HilbertOperator (Qubits active)) rowCurrent columnCurrent := by
  by_cases first : rowFirst = columnFirst
  · by_cases current : rowCurrent = columnCurrent
    · have same : prodEquiv (rowFirst, rowCurrent) =
          prodEquiv (columnFirst, columnCurrent) := congrArg prodEquiv (Prod.ext first current)
      simp only [Matrix.one_apply, if_pos same, if_pos first, if_pos current, mul_one]
    · have different : prodEquiv (rowFirst, rowCurrent) ≠
          prodEquiv (columnFirst, columnCurrent) := by
        intro same
        exact current (congrArg Prod.snd (prodEquiv.injective same))
      simp only [Matrix.one_apply, if_neg different, if_pos first, if_neg current, mul_zero]
  · have different : prodEquiv (rowFirst, rowCurrent) ≠
        prodEquiv (columnFirst, columnCurrent) := by
      intro same
      exact first (congrArg Prod.fst (prodEquiv.injective same))
    simp only [Matrix.one_apply, if_neg different, if_neg first, zero_mul]

private lemma tail_entry (before active after : Nat)
    (row column : (Qubits (before + (active + after))).Index) :
    segmentTailPreparation before active after row column =
      (1 : HilbertOperator (Qubits active))
        (segmentPartition before active after row).1
        (segmentPartition before active after column).1 *
      ((1 : HilbertOperator (Qubits before))
        (segmentPartition before active after row).2.1
        (segmentPartition before active after column).2.1 *
      uniformPreparation after (segmentPartition before active after row).2.2
        (segmentPartition before active after column).2.2) := by
  change (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits active))
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits before))
      (uniformPreparation after)))
        (segmentPartition before active after row) (segmentPartition before active after column) = _
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply,
    UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

private lemma future_entry (before after : Nat)
    (row column : (Qubits (before + after)).Index) :
    futurePreparation before after row column =
      (1 : HilbertOperator (Qubits before))
        ((prodEquiv (m := before) (n := after)).symm row).1
        ((prodEquiv (m := before) (n := after)).symm column).1 *
      uniformPreparation after
        ((prodEquiv (m := before) (n := after)).symm row).2
        ((prodEquiv (m := before) (n := after)).symm column).2 := by
  change (1 : HilbertOperator (Qubits before))
      ((prodEquiv (m := before) (n := after)).symm row).1
      ((prodEquiv (m := before) (n := after)).symm column).1 *
    uniformPreparation after
      ((prodEquiv (m := before) (n := after)).symm row).2
      ((prodEquiv (m := before) (n := after)).symm column).2 = _
  rfl

/-- The untouched later tensor is precisely the next future tensor on the same binary labels. -/
lemma window_source_segmentTail_advance (before active after : Nat) :
    UnitaryOperator.reindex (finPowAssoc before active after)
        (segmentTailPreparation before active after) =
      futurePreparation (before + active) after := by
  apply Subtype.ext
  ext row column
  obtain ⟨originalRow, rfl⟩ := (finPowAssoc before active after).surjective row
  obtain ⟨originalColumn, rfl⟩ := (finPowAssoc before active after).surjective column
  obtain ⟨⟨rowFirst, rowTail⟩, rfl⟩ :=
    (prodEquiv (m := before) (n := active + after)).surjective originalRow
  obtain ⟨⟨rowCurrent, rowAfter⟩, rfl⟩ :=
    (prodEquiv (m := active) (n := after)).surjective rowTail
  obtain ⟨⟨columnFirst, columnTail⟩, rfl⟩ :=
    (prodEquiv (m := before) (n := active + after)).surjective originalColumn
  obtain ⟨⟨columnCurrent, columnAfter⟩, rfl⟩ :=
    (prodEquiv (m := active) (n := after)).surjective columnTail
  change segmentTailPreparation before active after
      ((finPowAssoc before active after).symm
        (finPowAssoc before active after (prodEquiv (rowFirst, prodEquiv (rowCurrent, rowAfter)))))
      ((finPowAssoc before active after).symm
        (finPowAssoc before active after
          (prodEquiv (columnFirst, prodEquiv (columnCurrent, columnAfter))))) = _
  simp only [Equiv.symm_apply_apply]
  rw [tail_entry,
    window_source_segmentPartition_prod before active after rowFirst rowCurrent rowAfter,
    window_source_segmentPartition_prod before active after columnFirst columnCurrent columnAfter,
    prodEquiv_associative before active after rowFirst rowCurrent rowAfter,
    prodEquiv_associative before active after columnFirst columnCurrent columnAfter,
    future_entry]
  have rowSplit := (prodEquiv (m := before + active) (n := after)).symm_apply_apply
    (prodEquiv (rowFirst, rowCurrent), rowAfter)
  have columnSplit := (prodEquiv (m := before + active) (n := after)).symm_apply_apply
    (prodEquiv (columnFirst, columnCurrent), columnAfter)
  rw [rowSplit, columnSplit]
  change (1 : HilbertOperator (Qubits active)) rowCurrent columnCurrent *
      ((1 : HilbertOperator (Qubits before)) rowFirst columnFirst *
        uniformPreparation after rowAfter columnAfter) =
    (1 : HilbertOperator (Qubits (before + active)))
      (prodEquiv (rowFirst, rowCurrent)) (prodEquiv (columnFirst, columnCurrent)) *
      uniformPreparation after rowAfter columnAfter
  rw [combined_identity before active rowFirst columnFirst rowCurrent columnCurrent]
  ring

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
