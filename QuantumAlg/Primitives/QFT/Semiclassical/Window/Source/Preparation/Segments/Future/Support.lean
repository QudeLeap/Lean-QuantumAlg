/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Future
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Splitting the remaining mathematical preparation on its complete zero support

The consumed prefix is arbitrary and remains unchanged. Only the internally
unprepared suffix is zero. Preparing its current and later blocks separately
has the same complete columns, mixed density and external correlations as
preparing the combined suffix. These operators are mathematical source
coordinates; they introduce no physical preparation or allocated systems.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open NormalizedVector

/-- Exactly the remaining source coordinates are unprepared; the past prefix is unrestricted. -/
def futureZero (beforeWidth remaining : Nat)
    (label : (Qubits (beforeWidth + remaining)).Index) : Prop :=
  ((prodEquiv (m := beforeWidth) (n := remaining)).symm label).2 = 0

private lemma zero_pair (left right : Nat) :
    (prodEquiv (m := left) (n := right)).symm 0 = (0, 0) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]
  · apply Fin.ext
    simp only [prodEquiv_symm_snd_val, Fin.val_zero, Nat.zero_mod]

/-- The arbitrary consumed prefix retains its column; only the suffix becomes uniform. -/
lemma window_source_futurePreparation_zero_suffix (beforeWidth remaining : Nat)
    (row column : (Qubits (beforeWidth + remaining)).Index)
    (zero : futureZero beforeWidth remaining column) :
    futurePreparation beforeWidth remaining row column =
      (1 : HilbertOperator (Qubits beforeWidth))
        ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).1
        ((prodEquiv (m := beforeWidth) (n := remaining)).symm column).1 *
          invSqrt2 ^ remaining := by
  change (1 : HilbertOperator (Qubits beforeWidth))
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).1
      ((prodEquiv (m := beforeWidth) (n := remaining)).symm column).1 *
    uniformPreparation remaining
    ((prodEquiv (m := beforeWidth) (n := remaining)).symm row).2
    ((prodEquiv (m := beforeWidth) (n := remaining)).symm column).2 = _
  rw [show ((prodEquiv (m := beforeWidth) (n := remaining)).symm column).2 = 0 from zero,
    window_source_uniformPreparation_zero_column]

/-- Current/later preparation agrees for every full column whose remaining source is zero. -/
lemma window_source_splitFuturePreparation_zero_suffix (beforeWidth active later : Nat)
    (row column : (Qubits (beforeWidth + (active + later))).Index)
    (zero : futureZero beforeWidth (active + later) column) :
    splitFuturePreparation beforeWidth active later row column =
      futurePreparation beforeWidth (active + later) row column := by
  change (1 : HilbertOperator (Qubits beforeWidth))
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).1
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm column).1 *
    (uniformPreparation active
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).2).1
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm column).2).1 *
      uniformPreparation later
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).2).2
      ((prodEquiv (m := active) (n := later)).symm
        ((prodEquiv (m := beforeWidth) (n := active + later)).symm column).2).2) = _
  rw [window_source_futurePreparation_zero_suffix beforeWidth (active + later) row column zero]
  rw [show ((prodEquiv (m := beforeWidth) (n := active + later)).symm column).2 = 0 from zero,
    zero_pair, window_source_uniformPreparation_zero_column,
    window_source_uniformPreparation_zero_column]
  exact congrArg (fun scalar : Complex =>
    (1 : HilbertOperator (Qubits beforeWidth))
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm row).1
      ((prodEquiv (m := beforeWidth) (n := active + later)).symm column).1 * scalar)
    (pow_add (invSqrt2 : Complex) active later).symm

/-- All off-diagonal source entries agree on the internally established zero suffix. -/
lemma window_source_splitFuturePreparation_density (beforeWidth active later : Nat)
    (state : DensityOperator (Qubits (beforeWidth + (active + later))))
    (supported : ∀ label, ¬futureZero beforeWidth (active + later) label →
      state.matrix label label = 0) :
    DensityOperator.applyUnitary (splitFuturePreparation beforeWidth active later) state =
      DensityOperator.applyUnitary (futurePreparation beforeWidth (active + later)) state := by
  apply DensityOperator.ext
  apply DensityOperator.conjugation_eq_on_basis_support state
    (futureZero beforeWidth (active + later)) _ _ supported
  intro column zero row
  exact window_source_splitFuturePreparation_zero_suffix beforeWidth active later row column zero

/-- The same split keeps all physical, consumed-prefix and arbitrary-reference correlations. -/
lemma window_source_splitFuturePreparation_reference_density
    (Local Reference : Register) (beforeWidth active later : Nat)
    (state : DensityOperator
      (Local.prod ((Qubits (beforeWidth + (active + later))).prod Reference)))
    (supported : ∀ label, ¬futureZero beforeWidth (active + later) label.2.1 →
      state.matrix label label = 0) :
    DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (1 : UnitaryOperator Local)
          (UnitaryOperator.prodTensor (splitFuturePreparation beforeWidth active later)
            (1 : UnitaryOperator Reference))) state =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (1 : UnitaryOperator Local)
          (UnitaryOperator.prodTensor (futurePreparation beforeWidth (active + later))
            (1 : UnitaryOperator Reference))) state := by
  apply DensityOperator.ext
  apply DensityOperator.conjugation_eq_on_basis_support state
    (fun label => futureZero beforeWidth (active + later) label.2.1) _ _ supported
  intro column zero row
  simp only [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rw [window_source_splitFuturePreparation_zero_suffix beforeWidth active later
    row.2.1 column.2.1 zero]

/-- Every original Store, service state and chronological record retains this exact split. -/
lemma window_source_splitFuturePreparation_state {Record : Type} [Fintype Record]
    (Local Reference : Register) (beforeWidth active later : Nat)
    (state : ExecutionState Record
      (Local.prod ((Qubits (beforeWidth + (active + later))).prod Reference)))
    (supported : ∀ record label, ¬futureZero beforeWidth (active + later) label.2.1 →
      (state.block record).matrix label label = 0) :
    state.applyUnitary (fun _ =>
        UnitaryOperator.prodTensor (1 : UnitaryOperator Local)
          (UnitaryOperator.prodTensor (splitFuturePreparation beforeWidth active later)
            (1 : UnitaryOperator Reference))) =
      state.applyUnitary (fun _ =>
        UnitaryOperator.prodTensor (1 : UnitaryOperator Local)
          (UnitaryOperator.prodTensor (futurePreparation beforeWidth (active + later))
            (1 : UnitaryOperator Reference))) := by
  apply ExecutionState.ext
  intro record
  simp only [ExecutionState.applyUnitary_block]
  exact window_source_splitFuturePreparation_reference_density Local Reference
    beforeWidth active later (state.block record) (supported record)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
