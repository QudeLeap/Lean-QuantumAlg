/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments

/-!
# Preparing only the not-yet-consumed mathematical source

Consumed coordinates remain literal identity factors. Splitting the future
source into its current block and suffix has the same complete zero column
as preparing their combined width. This is a symbolic coordinate law on
the source observation space, not a physical preparation or permutation.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

/-- Retain the entire consumed prefix while preparing the remaining mathematical source. -/
def futurePreparation (beforeWidth remaining : Nat) :
    UnitaryOperator (Qubits (beforeWidth + remaining)) :=
  UnitaryOperator.reindex (prodEquiv (m := beforeWidth) (n := remaining))
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits beforeWidth))
      (uniformPreparation remaining))

/-- Prepare current and later blocks separately, keeping every consumed source coordinate. -/
def splitFuturePreparation (beforeWidth active later : Nat) :
    UnitaryOperator (Qubits (beforeWidth + (active + later))) :=
  UnitaryOperator.reindex (prodEquiv (m := beforeWidth) (n := active + later))
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits beforeWidth))
      (UnitaryOperator.reindex (S := Qubits (active + later))
        (prodEquiv (m := active) (n := later))
        (UnitaryOperator.prodTensor (uniformPreparation active) (uniformPreparation later))))

private lemma zero_split (left right : Nat) :
    (prodEquiv (m := left) (n := right)).symm 0 = (0, 0) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]
  · apply Fin.ext
    simp only [prodEquiv_symm_snd_val, Fin.val_zero, Nat.zero_mod]

/-- Future preparation leaves the consumed prefix exactly zero and is uniform on the suffix. -/
lemma window_source_futurePreparation_zero_column (beforeWidth remaining : Nat)
    (row : (Qubits (beforeWidth + remaining)).Index) :
    futurePreparation beforeWidth remaining row 0 =
      (if ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).1 = 0
        then (1 : Complex) else 0) * invSqrt2 ^ remaining := by
  change (1 : HilbertOperator (Qubits beforeWidth))
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).1
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm 0).1 *
    uniformPreparation remaining
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).2
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm 0).2 = _
  rw [zero_split, window_source_uniformPreparation_zero_column, Matrix.one_apply]

/-- Separate current/suffix preparation has that same complete zero column. -/
lemma window_source_splitFuturePreparation_zero_column (beforeWidth active later : Nat)
    (row : (Qubits (beforeWidth + (active + later))).Index) :
    splitFuturePreparation beforeWidth active later row 0 =
      futurePreparation beforeWidth (active + later) row 0 := by
  change (1 : HilbertOperator (Qubits beforeWidth))
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).1
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm 0).1 *
    (uniformPreparation active
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).2).1
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm 0).2).1 *
    uniformPreparation later
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).2).2
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm 0).2).2) = _
  rw [window_source_futurePreparation_zero_column, zero_split, zero_split,
    window_source_uniformPreparation_zero_column, window_source_uniformPreparation_zero_column,
    Matrix.one_apply]
  exact congrArg (fun scalar : Complex =>
    (if ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).1 = 0
      then (1 : Complex) else 0) * scalar)
    (pow_add (invSqrt2 : Complex) active later).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
