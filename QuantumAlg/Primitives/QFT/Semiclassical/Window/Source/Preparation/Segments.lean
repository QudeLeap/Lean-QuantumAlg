/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Contiguous mathematical source segments

The original binary label is partitioned into its consumed prefix, current
block and remaining suffix. All widths stay symbolic, including empty
segments. These are coordinates and preparation operators of the source
observation space; they allocate no physical register or executable swap.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

/-- The unchanged big-endian source label, with the current block selected first. -/
def segmentPartition (prefixWidth active suffix : Nat) :
    (Qubits (prefixWidth + (active + suffix))).Index ≃
      (Qubits active).Index × ((Qubits prefixWidth).prod (Qubits suffix)).Index :=
  (prodEquiv (m := prefixWidth) (n := active + suffix)).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) (prodEquiv (m := active) (n := suffix)).symm).trans
      { toFun := fun value => (value.2.1, (value.1, value.2.2))
        invFun := fun value => (value.2.1, (value.1, value.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })

/-- Original prefix, current and suffix labels survive the partition exactly. -/
lemma window_source_segmentPartition_prod (prefixWidth active suffix : Nat)
    (before : (Qubits prefixWidth).Index) (current : (Qubits active).Index)
    (after : (Qubits suffix).Index) :
    segmentPartition prefixWidth active suffix (prodEquiv (before, prodEquiv (current, after))) =
      (current, (before, after)) := by
  simp only [segmentPartition, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.coe_fn_mk, Prod.map_apply]

/-- The current block uses its literal original contiguous big-endian positions. -/
lemma window_source_segmentPartition_coordinate (prefixWidth active suffix : Nat)
    (label : (Qubits (prefixWidth + (active + suffix))).Index) (index : Fin active) :
    (BinaryBasis.bigEndianEquiv active).symm
        (segmentPartition prefixWidth active suffix label).1 index =
      (BinaryBasis.bigEndianEquiv (prefixWidth + (active + suffix))).symm label
        (Fin.natAdd prefixWidth (Fin.castAdd suffix index)) := by
  let split := (prodEquiv (m := prefixWidth) (n := active + suffix)).symm label
  let tail := (prodEquiv (m := active) (n := suffix)).symm split.2
  have original : label = prodEquiv (split.1, prodEquiv (tail.1, tail.2)) := by
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [original, window_source_segmentPartition_prod,
    BinaryBasis.bigEndianEquiv_prod_right, BinaryBasis.bigEndianEquiv_prod_left]

/-- Tensor preparation on the three literal segments, still only a mathematical unitary. -/
def segmentPreparation (prefixWidth active suffix : Nat) :
    UnitaryOperator (Qubits (prefixWidth + (active + suffix))) :=
  UnitaryOperator.reindex (prodEquiv (m := prefixWidth) (n := active + suffix))
    (UnitaryOperator.prodTensor (uniformPreparation prefixWidth)
      (UnitaryOperator.reindex (S := Qubits (active + suffix))
        (prodEquiv (m := active) (n := suffix))
        (UnitaryOperator.prodTensor (uniformPreparation active) (uniformPreparation suffix))))

private lemma split_zero (left right : Nat) :
    (prodEquiv (m := left) (n := right)).symm 0 = (0, 0) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]
  · apply Fin.ext
    simp only [prodEquiv_symm_snd_val, Fin.val_zero, Nat.zero_mod]

/-- Preparing the three symbolic segments has the same complete uniform zero column. -/
lemma window_source_segmentPreparation_zero_column (prefixWidth active suffix : Nat)
    (row : (Qubits (prefixWidth + (active + suffix))).Index) :
    segmentPreparation prefixWidth active suffix row 0 =
      invSqrt2 ^ (prefixWidth + (active + suffix)) := by
  change uniformPreparation prefixWidth
      ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm row).1
      ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm 0).1 *
    (uniformPreparation active
        ((prodEquiv (m := active) (n := suffix)).symm
          ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm row).2).1
        ((prodEquiv (m := active) (n := suffix)).symm
          ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm 0).2).1 *
      uniformPreparation suffix
        ((prodEquiv (m := active) (n := suffix)).symm
          ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm row).2).2
        ((prodEquiv (m := active) (n := suffix)).symm
          ((prodEquiv (m := prefixWidth) (n := active + suffix)).symm 0).2).2) = _
  rw [split_zero, split_zero, window_source_uniformPreparation_zero_column,
    window_source_uniformPreparation_zero_column, window_source_uniformPreparation_zero_column,
    pow_add, pow_add]

/-- The segmented and ordinary mathematical preparations coincide on the original zero input. -/
lemma window_source_segmentPreparation_zero (prefixWidth active suffix : Nat) :
    (segmentPreparation prefixWidth active suffix).applyVec
        (NormalizedVector.ket (R := Qubits (prefixWidth + (active + suffix))) 0 :
          HilbertVector (Qubits (prefixWidth + (active + suffix)))) =
      (uniformPreparation (prefixWidth + (active + suffix))).applyVec
        (NormalizedVector.ket (R := Qubits (prefixWidth + (active + suffix))) 0 :
          HilbertVector (Qubits (prefixWidth + (active + suffix)))) := by
  ext row
  simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using
    (window_source_segmentPreparation_zero_column prefixWidth active suffix row).trans
      (window_source_uniformPreparation_zero_column (prefixWidth + (active + suffix)) row).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
