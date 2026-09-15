/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Assembly

/-!
# Exact joint state of actual measured scalar initialization

The same circuit interpreter executes both fixed preparations and all original
retained-cell allocations. Every output matrix entry is the prescribed two
fresh basis factors times the entire incoming context-reference entry. The
formula holds for arbitrary coherences, subnormalized states and histories.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

variable {Reference : Register} {History : Type} [Fintype History]

/-- Actual work preparation tensors the fixed auxiliary factor with the complete old joint state. -/
theorem auxiliary_entry (modulus count : Nat)
    (state : State (before modulus.size count) Reference History)
    (newRow newColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size count).register Reference).Index) :
    ((prepareAuxiliary modulus count).execute Reference state).quantumMarginal.matrix
      (auxiliaryAssembly modulus count (newRow, oldRow.1), oldRow.2)
      (auxiliaryAssembly modulus count (newColumn, oldColumn.1), oldColumn.2) =
      ((InPlacePreparation.preparation modulus).normalized.vec newRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepare_joined_entry state InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (preparation_fresh_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (preparation_wires_union InversePreparation.auxiliaryKey _
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size)
      (auxiliary_disjoint modulus.size count))
    (InPlacePreparation.preparation modulus) newRow newColumn oldRow oldColumn

/-- Actual original-cell retains preserve every entry of the full old joint quantum state. -/
theorem cells_entry (width count : Nat)
    (state : State ((InversePreparation.after width).disjointUnion
      (exponents width count) (auxiliary_disjoint width count))
      Reference History)
    (row column : (Register.prod
      ((InversePreparation.after width).disjointUnion (exponents width count)
        (auxiliary_disjoint width count)).register Reference).Index) :
    ((allocateCells width count).execute Reference state).quantumMarginal.matrix
      (cellsAssembly width count row.1, row.2) (cellsAssembly width count column.1, column.2) =
        state.quantumMarginal.matrix row column := by
  have marginal := MeasurementCells.allocateFramed_quantumMarginal
    (InversePreparation.after width) (exponents width count) 2 width
    (complete_disjoint width count) state
  let coordinates := MeasurementCells.framedJointBasisEquiv (InversePreparation.after width)
    (exponents width count) 2 width
    (complete_disjoint width count) Reference
  have entry := congrArg
    (fun density : DensityOperator (Register.prod (withCells width count).register
      Reference) => density.matrix (coordinates row) (coordinates column)) marginal
  refine entry.trans ?_
  change state.quantumMarginal.matrix (coordinates.symm (coordinates row))
    (coordinates.symm (coordinates column)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Actual selector preparation supplies its fixed factor beside the full old joint state. -/
theorem selector_entry (width count : Nat)
    (state : State (withCells width count) Reference History)
    (newRow newColumn : (indexedLayout width count).register.Index)
    (oldRow oldColumn :
      (Register.prod (withCells width count).register Reference).Index) :
    ((prepareSelector width count).execute Reference state).quantumMarginal.matrix
      (selectorAssembly width count (newRow, oldRow.1), oldRow.2)
      (selectorAssembly width count (newColumn, oldColumn.1), oldColumn.2) =
      ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newRow *
        star ((BasisPreparation.zero (indexedLayout width count)).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepare_joined_entry state (indexedKey width count) (indexedLayout width count)
    (selector_fresh width count) (selector_disjoint width count)
    (BasisPreparation.zero (indexedLayout width count)) newRow newColumn oldRow oldColumn

/-- Both actual preparations and all retains preserve the exact complete incoming coherence. -/
theorem initialize_entry (modulus count : Nat)
    (state : State (before modulus.size count) Reference History)
    (selectorRow selectorColumn : (indexedLayout modulus.size count).register.Index)
    (auxiliaryRow auxiliaryColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size count).register Reference).Index) :
    ((initializeWork modulus count).execute Reference state).quantumMarginal.matrix
      (initializedAssembly modulus count (selectorRow, auxiliaryRow, oldRow.1), oldRow.2)
      (initializedAssembly modulus count (selectorColumn, auxiliaryColumn, oldColumn.1),
        oldColumn.2) =
      ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec
          selectorColumn)) *
      (((InPlacePreparation.preparation modulus).normalized.vec auxiliaryRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec auxiliaryColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn) := by
  change (Circuit.execute (Circuit.seq (prepareAuxiliary modulus count)
    (.seq (allocateCells modulus.size count) (prepareSelector modulus.size count)))
      Reference state).quantumMarginal.matrix _ _ = _
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal]
  change ((prepareSelector modulus.size count).execute Reference
    ((allocateCells modulus.size count).execute Reference
      ((prepareAuxiliary modulus count).execute Reference state))).quantumMarginal.matrix
        (selectorAssembly modulus.size count (selectorRow,
          cellsAssembly modulus.size count
            (auxiliaryAssembly modulus count (auxiliaryRow, oldRow.1))),
            oldRow.2)
        (selectorAssembly modulus.size count (selectorColumn,
          cellsAssembly modulus.size count
            (auxiliaryAssembly modulus count (auxiliaryColumn, oldColumn.1))),
            oldColumn.2) = _
  let auxiliaryState := (prepareAuxiliary modulus count).execute Reference state
  let cellsState := (allocateCells modulus.size count).execute Reference auxiliaryState
  have selected := selector_entry modulus.size count cellsState selectorRow selectorColumn
    (cellsAssembly modulus.size count
      (auxiliaryAssembly modulus count (auxiliaryRow, oldRow.1)), oldRow.2)
    (cellsAssembly modulus.size count
      (auxiliaryAssembly modulus count (auxiliaryColumn, oldColumn.1)),
      oldColumn.2)
  have retained := cells_entry modulus.size count auxiliaryState
    (auxiliaryAssembly modulus count (auxiliaryRow, oldRow.1), oldRow.2)
    (auxiliaryAssembly modulus count (auxiliaryColumn, oldColumn.1), oldColumn.2)
  have prepared := auxiliary_entry modulus count state auxiliaryRow auxiliaryColumn oldRow oldColumn
  exact selected.trans (congrArg
    (fun value : ℂ =>
      ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (indexedLayout modulus.size count)).normalized.vec
          selectorColumn)) * value) (retained.trans prepared))

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
