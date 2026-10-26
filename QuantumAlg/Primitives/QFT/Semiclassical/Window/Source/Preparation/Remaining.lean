/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Advance
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Cast

/-!
# Remaining preparation at an original symbolic source offset

The full mathematical source carrier stays fixed. Proven width equalities
identify its consumed prefix and remaining suffix; only that suffix is
prepared. Adjacent windows therefore share the same later operator, without
changing any physical wire or actual execution Reference carrier.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open scoped Kronecker
open NormalizedVector

/-- Prepare the remaining suffix on the original full mathematical source. -/
def remainingPreparation (full consumed remaining : Nat) (widths : consumed + remaining = full) :
    UnitaryOperator (Qubits full) :=
  UnitaryOperator.reindex (finCongr (congrArg (fun width : Nat => 2 ^ width) widths))
    (futurePreparation consumed remaining)

/-- The same consumed offset determines the same remaining operator on the fixed carrier. -/
lemma window_source_remainingPreparation_congr
    (full firstBefore secondBefore firstAfter secondAfter : Nat)
    (firstWidth : firstBefore + firstAfter = full)
    (secondWidth : secondBefore + secondAfter = full) (before : firstBefore = secondBefore) :
    remainingPreparation full firstBefore firstAfter firstWidth =
      remainingPreparation full secondBefore secondAfter secondWidth := by
  subst secondBefore
  have same : firstAfter = secondAfter := Nat.add_left_cancel (firstWidth.trans secondWidth.symm)
  subst secondAfter
  rfl

/-- Consuming the current block leaves exactly the next suffix preparation. -/
lemma window_source_remainingPreparation_advance (full before active after : Nat)
    (widths : before + (active + after) = full) :
    UnitaryOperator.reindex (finCongr (congrArg (fun width : Nat => 2 ^ width) widths))
        (segmentTailPreparation before active after) =
      remainingPreparation full (before + active) after
        ((Nat.add_assoc before active after).trans widths) := by
  unfold remainingPreparation
  rw [← window_source_segmentTail_advance, UnitaryOperator.unitaryOperator_reindex_trans]
  have route : (finPowAssoc before active after).trans
      (finCongr (congrArg (fun width : Nat => 2 ^ width)
        ((Nat.add_assoc before active after).trans widths))) =
      finCongr (congrArg (fun width : Nat => 2 ^ width) widths) := by
    apply Equiv.ext
    intro label
    apply Fin.ext
    rfl
  rw [route]

lemma window_source_identity_tensor {R S : Register} :
    UnitaryOperator.prodTensor (1 : UnitaryOperator R) (1 : UnitaryOperator S) = 1 := by
  apply Subtype.ext
  change Matrix.reindex (Register.prodIndexEquiv R S) (Register.prodIndexEquiv R S)
    ((1 : HilbertOperator R) ⊗ₖ (1 : HilbertOperator S)) = _
  rw [Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  rfl

/-- No unconsumed source bits means literal identity on the complete source. -/
lemma window_source_remainingPreparation_empty (full consumed : Nat)
    (widths : consumed + 0 = full) : remainingPreparation full consumed 0 widths = 1 := by
  unfold remainingPreparation futurePreparation
  change UnitaryOperator.reindex _
    (UnitaryOperator.reindex _
      (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits consumed))
        (1 : UnitaryOperator (Qubits 0)))) = 1
  rw [window_source_identity_tensor, UnitaryOperator.unitaryOperator_reindex_one,
    UnitaryOperator.unitaryOperator_reindex_one]

/-- Preparing the original whole zero source gives its exact uniform column. -/
lemma window_source_remainingPreparation_start_column (full : Nat)
    (widths : 0 + full = full) (row : (Qubits full).Index) :
    remainingPreparation full 0 full widths row 0 = invSqrt2 ^ full := by
  let coordinates := finCongr (congrArg (fun width : Nat => 2 ^ width) widths)
  have zero : coordinates.symm 0 = 0 := by
    apply Fin.ext
    rfl
  change futurePreparation 0 full (coordinates.symm row) (coordinates.symm 0) = _
  rw [zero, window_source_futurePreparation_zero_column]
  have prefixZero : ((prodEquiv (m := 0) (n := full)).symm (coordinates.symm row)).1 = 0 :=
    Fin.fin_one_eq_zero _
  rw [if_pos prefixZero, one_mul]

/-- Remaining preparation on the original pair, with no change to that mathematical carrier. -/
def pairedRemainingPreparation (bits consumed remaining : Nat)
    (widths : consumed + remaining = bits + bits) :
    UnitaryOperator ((Qubits bits).prod (Qubits bits)) :=
  UnitaryOperator.reindex (prodEquiv (m := bits) (n := bits)).symm
    (remainingPreparation (bits + bits) consumed remaining widths)

/-- The original paired-label coordinates describe the same future preparation. -/
lemma window_sourcePaired_remaining_future (bits before active after : Nat)
    (widths : before + (active + after) = bits + bits) :
    UnitaryOperator.reindex (pairedLabelEquiv bits _ widths).symm
        (futurePreparation before (active + after)) =
      pairedRemainingPreparation bits before (active + after) widths := by
  apply Subtype.ext
  rfl

/-- The exact later tensor on the same pair is preparation at the next consumed offset. -/
lemma window_sourcePaired_remaining_tail (bits before active after : Nat)
    (widths : before + (active + after) = bits + bits) :
    UnitaryOperator.reindex (pairedLabelEquiv bits _ widths).symm
        (segmentTailPreparation before active after) =
      pairedRemainingPreparation bits (before + active) after
        ((Nat.add_assoc before active after).trans widths) := by
  have coordinates :
      UnitaryOperator.reindex (pairedLabelEquiv bits _ widths).symm
          (segmentTailPreparation before active after) =
        UnitaryOperator.reindex (R := Qubits (bits + bits))
          (S := (Qubits bits).prod (Qubits bits))
          (prodEquiv (m := bits) (n := bits)).symm
          (UnitaryOperator.reindex (S := Qubits (bits + bits))
            (finCongr (congrArg (fun width : Nat => 2 ^ width) widths))
            (segmentTailPreparation before active after)) := by
    apply Subtype.ext
    rfl
  exact coordinates.trans
    (congrArg (fun operator : UnitaryOperator (Qubits (bits + bits)) =>
      UnitaryOperator.reindex (R := Qubits (bits + bits))
        (S := (Qubits bits).prod (Qubits bits))
        (prodEquiv (m := bits) (n := bits)).symm operator)
      (window_source_remainingPreparation_advance (bits + bits) before active after widths))

/-- A proved same consumed offset determines the same operator on the original pair. -/
lemma window_sourcePaired_remaining_congr
    (bits firstBefore secondBefore firstAfter secondAfter : Nat)
    (firstWidth : firstBefore + firstAfter = bits + bits)
    (secondWidth : secondBefore + secondAfter = bits + bits)
    (before : firstBefore = secondBefore) :
    pairedRemainingPreparation bits firstBefore firstAfter firstWidth =
      pairedRemainingPreparation bits secondBefore secondAfter secondWidth := by
  subst secondBefore
  have same : firstAfter = secondAfter := Nat.add_left_cancel (firstWidth.trans secondWidth.symm)
  subst secondAfter
  rfl

/-- After the final original pair coordinate, the full mathematical source is unchanged. -/
lemma window_sourcePaired_remaining_empty (bits consumed remaining : Nat)
    (widths : consumed + remaining = bits + bits) (empty : remaining = 0) :
    pairedRemainingPreparation bits consumed remaining widths = 1 := by
  subst remaining
  unfold pairedRemainingPreparation
  rw [window_source_remainingPreparation_empty, UnitaryOperator.unitaryOperator_reindex_one]

/-- The original whole paired zero source has the same two full uniform H amplitudes. -/
lemma window_sourcePaired_remaining_start_column (bits : Nat)
    (widths : 0 + (bits + bits) = bits + bits)
    (row : ((Qubits bits).prod (Qubits bits)).Index) :
    pairedRemainingPreparation bits 0 (bits + bits) widths row (0, 0) =
      uniformPreparation bits row.1 0 * uniformPreparation bits row.2 0 := by
  have zero : (prodEquiv (m := bits) (n := bits)) (0, 0) = 0 := by
    apply Fin.ext
    change 0 + 2 ^ bits * 0 = 0
    rw [Nat.mul_zero, Nat.zero_add]
  change remainingPreparation (bits + bits) 0 (bits + bits) widths
    (prodEquiv row) (prodEquiv (0, 0)) = _
  rw [zero, window_source_remainingPreparation_start_column,
    window_source_uniformPreparation_zero_column, window_source_uniformPreparation_zero_column,
    pow_add]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
