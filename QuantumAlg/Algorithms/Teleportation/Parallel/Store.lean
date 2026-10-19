/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Teleportation.Parallel.Readout
import all QuantumAlg.Algorithms.Teleportation.Parallel.Readout
import all QuantumAlg.Algorithms.Teleportation.Parallel.Geometry
import all QuantumAlg.Core.Execution.Measurement.Cells.Store.Ext
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp

/-!
# Complete measured stores forget only overwritten result values

The protocol has no unmeasured classical payload: the original quantum
entries carry presence markers, and all retained result cells are really
overwritten by Z measurement. The final complete store is consequently
determined by Alice's measured labels, even when the original cell values
were correlated with the unknown quantum input [dW19, qcnotes.tex:802].
-/

namespace QuantumAlg.QuantumTeleportation.Parallel

noncomputable section

open Execution

private instance quantumStore_subsingleton (count : Nat) :
    Subsingleton (Store (quantumContext count)) where
  allEq first second := by
    apply congrArg Store.mk
    exact Subsingleton.elim (α := Unit × Unit) first.cells second.cells

private lemma finiteValue_eq {dimension : ℕ+}
    (first second : CShape.Value (.finite dimension))
    (same : first.toFin.val = second.toFin.val) : first = second := by
  cases first with
  | finite first =>
      cases second with
      | finite second => exact congrArg CShape.Value.finite (Fin.ext same)

/-- Equality of all measured finite values is equality of the actual complete final store. -/
lemma store_eq_of_resultValues (count : Nat) (first second : Store (context count))
    (same : ∀ index : Fin (count * 2),
      (first.read (.storage (resultCell count index).toCStorageRef)).toFin.val =
        (second.read (.storage (resultCell count index).toCStorageRef)).toFin.val) :
    first = second := by
  apply MeasurementCells.store_eq_of_reference_reads (quantumContext count) 2 (count * 2)
  intro index
  exact finiteValue_eq _ _ (same index)

/-- The actual write condition depends only on the measured labels, never old result contents. -/
lemma writtenStore_eq_iff (count : Nat) (original stored : Store (context count))
    (basis : (context count).register.Index) :
    writtenStore count original basis = stored ↔
      ∀ index : Fin (count * 2),
        (basis (measuredPosition count index)).val =
          (stored.read (.storage (resultCell count index).toCStorageRef)).toFin.val := by
  constructor
  · intro same index
    rw [← same]
    exact (writtenStore_value count original basis index).symm
  · intro same
    apply store_eq_of_resultValues
    intro index
    exact (writtenStore_value count original basis index).trans (same index)

/-- Every old result cell is overwritten; this makes no assumption about its prior correlations. -/
lemma writtenStore_independent (count : Nat) (first second : Store (context count))
    (basis : (context count).register.Index) :
    writtenStore count first basis = writtenStore count second basis := by
  apply store_eq_of_resultValues
  intro index
  exact (writtenStore_value count first basis index).trans
    (writtenStore_value count second basis index).symm

end

end QuantumAlg.QuantumTeleportation.Parallel
