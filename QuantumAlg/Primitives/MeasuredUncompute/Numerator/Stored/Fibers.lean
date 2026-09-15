/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Measurement.Cells.Store.Ext
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Projection

/-!
# Exact stored-result fibers of the complete measured arithmetic frame

The complete original frame has only quantum entries. Its n retained finite
measurement cells are therefore all of its actual classical data. Writing
the actual Z outcomes overwrites every one of those cells and keeps exactly
one final store for each n-bit outcome. The source density of each such
fiber is the original complete quantum-reference marginal, without any
initial classical-value assumption
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorStoredFibers

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private instance initial_store_unique (width : Nat) :
    Subsingleton (Store (InversePreparation.after width)) :=
  ⟨fun first second => by
    apply congrArg Store.mk
    exact Subsingleton.elim (α := Unit × (Unit × Unit)) first.cells second.cells⟩

private theorem finite_value_eq (first second : CShape.Value (.finite 2))
    (same : decide (first.toFin.val = 1) = decide (second.toFin.val = 1)) : first = second := by
  cases first with
  | finite first =>
      cases second with
      | finite second =>
          change decide (first.val = 1) = decide (second.val = 1) at same
          fin_cases first <;> fin_cases second <;> simp_all

/-- The actual finite outcomes determine the whole store, including width zero. -/
theorem outcome_injective (width : Nat) :
    Function.Injective (fun store : Store (context width) =>
      NumeratorReset.outcome (store.read (input width))) := by
  intro first second same
  apply MeasurementCells.store_eq_of_reference_reads (InversePreparation.after width) 2 width
  intro index
  apply finite_value_eq
  have bits := congrArg (fun value : Fin (2 ^ width) => value.val.testBit index.val) same
  exact (NumeratorReset.outcome_bit (first.read (input width)) index).symm.trans
    (bits.trans (NumeratorReset.outcome_bit (second.read (input width)) index))

/-- The actual measurement writes every classical cell to the specified real final store. -/
theorem write_representative (width : Nat) (original stored : Store (context width)) :
    Circuit.writeMeasurementPath (readouts width) original
      (Circuit.measurementBasisPath (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored := by
  apply outcome_injective width
  exact (stored_outcome width original _).trans
    (NumeratorStoredProjection.representative_word width _)

/-- Every final stored outcome has exactly the original full quantum-reference source density. -/
theorem source_eq_marginal (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width)) :
    NumeratorStoredProjection.source width state stored = state.quantumMarginal := by
  unfold NumeratorStoredProjection.source
  have selected : state.filterClassical (fun entry =>
      Circuit.writeMeasurementPath (readouts width) entry.1
        (Circuit.measurementBasisPath (readouts width)
          (NumeratorStoredProjection.representative width
            (NumeratorReset.outcome (stored.read (input width))))) = stored) = state := by
    apply ExecutionState.ext
    intro entry
    simp only [ExecutionState.filterClassical_block, write_representative, if_true]
  exact congrArg ExecutionState.quantumMarginal selected

/-- The finite labels enumerate actual stores; this equivalence allocates no packed register. -/
def outcomeEquiv (width : Nat) : Store (context width) ≃ Fin (2 ^ width) :=
  Equiv.ofBijective (fun store => NumeratorReset.outcome (store.read (input width)))
    ⟨outcome_injective width, fun value => by
      let original := Store.ofValues (context width) (fun _ _ shape _ => CShape.initialValue shape)
      refine ⟨Circuit.writeMeasurementPath (readouts width) original
        (Circuit.measurementBasisPath (readouts width)
          (NumeratorStoredProjection.representative width value)), ?_⟩
      exact (stored_outcome width original _).trans
        (NumeratorStoredProjection.representative_word width value)⟩

/-- There are exactly as many actual final stores as n-bit outcomes, including the empty vector. -/
theorem store_card (width : Nat) : Fintype.card (Store (context width)) = 2 ^ width :=
  (Fintype.card_congr (outcomeEquiv width)).trans (Fintype.card_fin _)

end

end QuantumAlg.MeasuredUncompute.NumeratorStoredFibers
