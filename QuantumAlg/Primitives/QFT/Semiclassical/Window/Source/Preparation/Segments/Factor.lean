/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Future
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Remainder
import Mathlib.Tactic.Ring

/-!
# Current and later preparation in the same mathematical source coordinates

The later tensor is identity on the current and consumed source blocks.
Applying it after the current selected preparation gives exactly the original
split-future operator. The widths remain symbolic, including empty blocks;
the proof uses tensor algebra and does not enumerate source labels or gates.
These are mathematical source operators, not physical instructions.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open scoped Kronecker

private lemma tensor_matrix {R S : Register}
    (first : UnitaryOperator R) (second : UnitaryOperator S) :
    (UnitaryOperator.prodTensor first second : HilbertOperator (R.prod S)) =
      (first : HilbertOperator R) ⊗ₖ (second : HilbertOperator S) := by
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

private lemma tensor_mul {R S : Register}
    (first second : UnitaryOperator R) (third fourth : UnitaryOperator S) :
    UnitaryOperator.prodTensor first third * UnitaryOperator.prodTensor second fourth =
      UnitaryOperator.prodTensor (first * second) (third * fourth) := by
  apply Subtype.ext
  change ((UnitaryOperator.prodTensor first third : HilbertOperator (R.prod S)) *
    (UnitaryOperator.prodTensor second fourth : HilbertOperator (R.prod S))) = _
  rw [tensor_matrix, tensor_matrix, tensor_matrix]
  exact (Matrix.mul_kronecker_mul (first : HilbertOperator R) (second : HilbertOperator R)
    (third : HilbertOperator S) (fourth : HilbertOperator S)).symm

/-- Prepare only the later mathematical block, preserving both the consumed and current blocks. -/
def segmentTailPreparation (beforeWidth active later : Nat) :
    UnitaryOperator (Qubits (beforeWidth + (active + later))) :=
  UnitaryOperator.reindex (segmentPartition beforeWidth active later).symm
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits active))
      (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits beforeWidth))
        (uniformPreparation later)))

/-- The exact current-then-later factorization of the unchanged split-future operator. -/
lemma window_source_splitFuturePreparation_factor (beforeWidth active later : Nat) :
    segmentTailPreparation beforeWidth active later *
        selectedUniformPreparation (segmentPartition beforeWidth active later) =
      splitFuturePreparation beforeWidth active later := by
  unfold segmentTailPreparation selectedUniformPreparation
  rw [← UnitaryOperator.unitaryOperator_reindex_mul, tensor_mul, one_mul, mul_one]
  apply Subtype.ext
  ext row column
  let rowSplit := (prodEquiv (m := beforeWidth) (n := active + later)).symm row
  let columnSplit := (prodEquiv (m := beforeWidth) (n := active + later)).symm column
  let rowTail := (prodEquiv (m := active) (n := later)).symm rowSplit.2
  let columnTail := (prodEquiv (m := active) (n := later)).symm columnSplit.2
  change uniformPreparation active rowTail.1 columnTail.1 *
      ((1 : HilbertOperator (Qubits beforeWidth)) rowSplit.1 columnSplit.1 *
        uniformPreparation later rowTail.2 columnTail.2) =
    (1 : HilbertOperator (Qubits beforeWidth)) rowSplit.1 columnSplit.1 *
      (uniformPreparation active rowTail.1 columnTail.1 *
        uniformPreparation later rowTail.2 columnTail.2)
  ring

private lemma identity_pair_entry {R S : Register} (row column : (R.prod S).Index) :
    (1 : HilbertOperator (R.prod S)) row column =
      (1 : HilbertOperator R) row.1 column.1 * (1 : HilbertOperator S) row.2 column.2 := by
  by_cases first : row.1 = column.1
  · by_cases second : row.2 = column.2
    · have same : row = column := Prod.ext first second
      simp only [Matrix.one_apply, if_pos same, if_pos first, if_pos second, mul_one]
    · have different : row ≠ column := fun same => second (congrArg Prod.snd same)
      simp only [Matrix.one_apply, if_neg different, if_pos first, if_neg second, mul_zero]
  · have different : row ≠ column := fun same => first (congrArg Prod.fst same)
    simp only [Matrix.one_apply, if_neg different, if_neg first, zero_mul]

/-- Saved-source preparation keeps literal identity on physical and reference coordinates. -/
lemma window_source_savedPreparation_reference {ctx : RuntimeCtx .quantum}
    {S Rest : Register} {active : Nat}
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index)
    (Reference : Register) (operator : UnitaryOperator Rest) :
    savedPreparation (ctx := ctx) partition Reference
        (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) =
      UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
        (UnitaryOperator.prodTensor
          (UnitaryOperator.reindex partition.symm
            (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits active)) operator))
          (1 : UnitaryOperator Reference)) := by
  apply Subtype.ext
  ext row column
  change (1 : HilbertOperator (ctx.register.prod (Qubits active)))
      (row.1, (partition row.2.1).1) (column.1, (partition column.2.1).1) *
    (operator (partition row.2.1).2 (partition column.2.1).2 *
      (1 : HilbertOperator Reference) row.2.2 column.2.2) =
    (1 : HilbertOperator ctx.register) row.1 column.1 *
      (((1 : HilbertOperator (Qubits active))
        (partition row.2.1).1 (partition column.2.1).1 *
          operator (partition row.2.1).2 (partition column.2.1).2) *
        (1 : HilbertOperator Reference) row.2.2 column.2.2)
  rw [identity_pair_entry]
  ring

/-- The later mathematical tensor is the same full saved-coordinate preparation. -/
lemma window_source_segmentTail_reference {ctx : RuntimeCtx .quantum}
    (beforeWidth active later : Nat) (Reference : Register) :
    savedPreparation (ctx := ctx) (segmentPartition beforeWidth active later) Reference
        (UnitaryOperator.prodTensor
          (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits beforeWidth))
            (uniformPreparation later)) (1 : UnitaryOperator Reference)) =
      UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
        (UnitaryOperator.prodTensor (segmentTailPreparation beforeWidth active later)
          (1 : UnitaryOperator Reference)) :=
  window_source_savedPreparation_reference _ _ _

/-- Future preparation commutes with the current feed on the entire original source space. -/
lemma window_source_feed_segmentTail_commute {ctx : RuntimeCtx .quantum}
    {totalBits active : Nat} (ports : Ports ctx totalBits active)
    (beforeWidth later : Nat) (Reference : Register) :
    selectedFeedOperator ports (segmentPartition beforeWidth active later) Reference *
        UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
          (UnitaryOperator.prodTensor (segmentTailPreparation beforeWidth active later)
            (1 : UnitaryOperator Reference)) =
      UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
        (UnitaryOperator.prodTensor (segmentTailPreparation beforeWidth active later)
          (1 : UnitaryOperator Reference)) *
        selectedFeedOperator ports (segmentPartition beforeWidth active later) Reference := by
  rw [← window_source_segmentTail_reference]
  exact window_source_feed_saved_commute ports _ _ _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
