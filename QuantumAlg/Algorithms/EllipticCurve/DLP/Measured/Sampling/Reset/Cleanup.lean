/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Pure
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Cleanup

/-!
# Physical restart certificate for the actual sampling reset

The terminal sampling context owns every quantum wire. Its original public
points are borrowed classical values. The complete executed reset measures a
physical system on every path, preserves those borrowed values, and prepares
one fixed quantum seed on every complete outcome record.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement

private theorem cells_borrowedQuantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (dimension : ℕ+) (count : Nat) :
    (MeasurementCells.context ctx dimension count).borrowedQuantumWires =
      ctx.borrowedQuantumWires := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa only [MeasurementCells.context, RuntimeCtx.borrowedQuantumWires_addRetained]
        using ih

private theorem union_borrowedQuantumWires {kind : ProblemKind}
    (left right : RuntimeCtx kind) (disjoint : RuntimeCtx.StorageDisjoint left right) :
    (left.disjointUnion right disjoint).borrowedQuantumWires =
      left.borrowedQuantumWires ++ right.borrowedQuantumWires := by
  simp only [RuntimeCtx.borrowedQuantumWires, RuntimeCtx.disjointUnion,
    List.flatMap_append]

private theorem indexedEntries_noBorrowedQuantum (width : Nat) (indices : List Nat) :
    (indices.map (indexedEntry width)).flatMap RuntimeEntry.borrowedQuantumWires = [] := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      simpa only [List.map_cons, List.flatMap_cons, indexedEntry,
        RuntimeEntry.borrowedQuantumWires, List.nil_append] using ih

private theorem indexed_noBorrowedQuantum (width : Nat) (indices : List Nat)
    (distinct : indices.Nodup) :
    (indexedContext width indices distinct).borrowedQuantumWires = [] :=
  indexedEntries_noBorrowedQuantum width indices

/-- The actual terminal context borrows no quantum wire; its public frame is classical. -/
theorem PublicInput.terminal_noBorrowedQuantum {p : Nat}
    (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat) :
    (PublicInput.terminal E exponentWidth).borrowedQuantumWires = [] := by
  have original :
      (MAU.Inversion.SharedEEA.InversePreparation.before p.size).borrowedQuantumWires =
        [] := rfl
  have auxiliary :
      (MAU.Inversion.SharedEEA.InversePreparation.after p.size).borrowedQuantumWires =
        [] := by
    simpa only [MAU.Inversion.SharedEEA.InversePreparation.after,
      RuntimeCtx.borrowedQuantumWires_addOwnedLayout] using original
  have numerator :
      (MeasuredUncompute.NumeratorMeasurement.context p.size).borrowedQuantumWires =
        [] := by
    simpa only [MeasuredUncompute.NumeratorMeasurement.context,
      cells_borrowedQuantumWires] using auxiliary
  have exponents :
      (Allocation.exponents p.size (2 * exponentWidth)).borrowedQuantumWires = [] := by
    exact indexed_noBorrowedQuantum p.size (List.range (2 * exponentWidth))
      List.nodup_range
  have withCells :
      (Allocation.withCells p.size (2 * exponentWidth)).borrowedQuantumWires = [] := by
    rw [Allocation.withCells, union_borrowedQuantumWires, numerator, exponents]
    rfl
  have after :
      (Allocation.after p.size (2 * exponentWidth)).borrowedQuantumWires = [] := by
    simpa only [Allocation.after, RuntimeCtx.borrowedQuantumWires_addOwnedLayout]
      using withCells
  have terminalBase :
      (exponentMeasurementContext p exponentWidth).borrowedQuantumWires = [] := by
    simpa only [exponentMeasurementContext, cells_borrowedQuantumWires] using after
  have frame : (PublicInput.frame E exponentWidth).borrowedQuantumWires = [] := rfl
  rw [PublicInput.terminal, union_borrowedQuantumWires, terminalBase, frame]
  rfl

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- The original physical sampling reset uses its specified complete basis
label for every input and complete execution record. -/
theorem samplingReset_reinitializedAt :
    Circuit.ReinitializedAt
      (samplingReset E fieldTail exponentWidth sameWidth fits seed)
      ((PublicInput.terminal E exponentWidth).quantumLayout.restrictSelectedBasis
        (PublicInput.terminal E exponentWidth).borrowedSelectionᶜ
        (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)) :=
  QuditShift.resetToBasis_reinitializedAt
    (samplingResetImplementations E exponentWidth)
    (samplingResetCells E exponentWidth)
    (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)
    (PublicInput.terminal_noBorrowedQuantum E exponentWidth)

/-- The complete actual sampling reset has a physical restart certificate. -/
theorem samplingReset_restartCleanup :
    Circuit.RestartCleanup (samplingReset E fieldTail exponentWidth sameWidth fits seed) := by
  let selector : Fin (Allocation.after p.size (2 * exponentWidth)).systemCount :=
    ⟨0, Allocation.after_systemCount_pos p.size (2 * exponentWidth)⟩
  let inCells := MeasurementCells.wireEquiv
    (Allocation.after p.size (2 * exponentWidth)) 2 (2 * exponentWidth) selector
  let inTerminal := ContextUnion.leftPosition
    (exponentMeasurementContext p exponentWidth) (PublicInput.frame E exponentWidth)
    (PublicInput.terminal_disjoint E exponentWidth) inCells
  have positive : 0 < (PublicInput.terminal E exponentWidth).systemCount :=
    lt_of_le_of_lt (Nat.zero_le inTerminal.val) inTerminal.isLt
  exact QuditShift.resetToBasis_restartCleanup
    (samplingResetImplementations E exponentWidth)
    (samplingResetCells E exponentWidth)
    (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)
    positive (PublicInput.terminal_noBorrowedQuantum E exponentWidth)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
