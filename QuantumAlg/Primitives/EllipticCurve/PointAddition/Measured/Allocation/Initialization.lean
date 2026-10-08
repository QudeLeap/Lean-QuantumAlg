/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation.Assembly
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Preparation.Framed.Entries

/-!
# Exact joint state of actual measured point-addition initialization

The same circuit interpreter executes both fixed preparations and all original
retained-cell allocations. Every output matrix entry is the prescribed two
fresh basis factors times the entire incoming context-reference entry. The
formula holds for arbitrary coherences, subnormalized states and histories.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

variable {Reference : Register} {History : Type} [Fintype History]

/-- Actual work preparation tensors the fixed auxiliary factor with the complete old joint state. -/
theorem auxiliary_entry (modulus : Nat) (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (newRow newColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size).register Reference).Index) :
    ((prepareAuxiliary modulus).execute Reference state).quantumMarginal.matrix
      (auxiliaryAssembly modulus (newRow, oldRow.1), oldRow.2)
      (auxiliaryAssembly modulus (newColumn, oldColumn.1), oldColumn.2) =
      ((InPlacePreparation.preparation modulus).normalized.vec newRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn :=
  InPlacePreparation.Framed.execute_joined_entry modulus
    (InPlaceControlled.controlContext modulus.size) (auxiliary_disjoint_control modulus.size)
    state newRow newColumn oldRow oldColumn

/-- Actual original-cell retains preserve every entry of the full old joint quantum state. -/
theorem cells_entry (width : Nat)
    (state : State ((InversePreparation.after width).disjointUnion
      (InPlaceControlled.controlContext width) (auxiliary_disjoint_control width))
      Reference (ClassicalOracleModel.empty.HiddenState × History))
    (row column : (Register.prod
      ((InversePreparation.after width).disjointUnion (InPlaceControlled.controlContext width)
        (auxiliary_disjoint_control width)).register Reference).Index) :
    ((allocateCells width).execute Reference state).quantumMarginal.matrix
      (cellsAssembly width row.1, row.2) (cellsAssembly width column.1, column.2) =
        state.quantumMarginal.matrix row column := by
  have marginal := MeasurementCells.allocateFramed_quantumMarginal
    (model := .quantum AlgorithmGate.model .empty)
    (InversePreparation.after width) (InPlaceControlled.controlContext width) 2 width
    (InPlaceControlled.control_disjoint width) state
  let coordinates := MeasurementCells.framedJointBasisEquiv (InversePreparation.after width)
    (InPlaceControlled.controlContext width) 2 width
    (InPlaceControlled.control_disjoint width) Reference
  have entry := congrArg
    (fun density : DensityOperator (Register.prod (InPlaceControlled.context width).register
      Reference) => density.matrix (coordinates row) (coordinates column)) marginal
  refine entry.trans ?_
  change state.quantumMarginal.matrix (coordinates.symm (coordinates row))
    (coordinates.symm (coordinates column)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Actual selector preparation supplies its fixed factor beside the full old joint state. -/
theorem selector_entry (width : Nat)
    (state : State (InPlaceControlled.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (newRow newColumn : (selectorLayout width).register.Index)
    (oldRow oldColumn :
      (Register.prod (InPlaceControlled.context width).register Reference).Index) :
    ((prepareSelector width).execute Reference state).quantumMarginal.matrix
      (selectorAssembly width (newRow, oldRow.1), oldRow.2)
      (selectorAssembly width (newColumn, oldColumn.1), oldColumn.2) =
      ((BasisPreparation.zero (selectorLayout width)).normalized.vec newRow *
        star ((BasisPreparation.zero (selectorLayout width)).normalized.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn :=
  Circuit.prepareZero_joined_entry (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty)
    state (selectorKey width) (selectorLayout width)
    (InPlaceControlled.context width).canonicalFreshKey_fresh (selector_physical_disjoint width)
    newRow newColumn oldRow oldColumn

/-- Both actual preparations and all retains preserve the exact complete incoming coherence. -/
theorem initialize_entry (modulus : Nat) (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (selectorRow selectorColumn : (selectorLayout modulus.size).register.Index)
    (auxiliaryRow auxiliaryColumn : (InputPreparation.auxiliaryLayout modulus.size).register.Index)
    (oldRow oldColumn : (Register.prod (before modulus.size).register Reference).Index) :
    ((initializeWork modulus).execute Reference state).quantumMarginal.matrix
      (initializedAssembly modulus (selectorRow, auxiliaryRow, oldRow.1), oldRow.2)
      (initializedAssembly modulus (selectorColumn, auxiliaryColumn, oldColumn.1), oldColumn.2) =
      ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec
          selectorColumn)) *
      (((InPlacePreparation.preparation modulus).normalized.vec auxiliaryRow *
        star ((InPlacePreparation.preparation modulus).normalized.vec auxiliaryColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn) := by
  change (Circuit.execute (Circuit.seq (prepareAuxiliary modulus)
    (.seq (allocateCells modulus.size) (prepareSelector modulus.size)))
      Reference state).quantumMarginal.matrix _ _ = _
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal]
  change ((prepareSelector modulus.size).execute Reference
    ((allocateCells modulus.size).execute Reference
      ((prepareAuxiliary modulus).execute Reference state))).quantumMarginal.matrix
        (selectorAssembly modulus.size (selectorRow,
          cellsAssembly modulus.size (auxiliaryAssembly modulus (auxiliaryRow, oldRow.1))),
            oldRow.2)
        (selectorAssembly modulus.size (selectorColumn,
          cellsAssembly modulus.size (auxiliaryAssembly modulus (auxiliaryColumn, oldColumn.1))),
            oldColumn.2) = _
  let auxiliaryState := (prepareAuxiliary modulus).execute Reference state
  let cellsState := (allocateCells modulus.size).execute Reference auxiliaryState
  have selected := selector_entry modulus.size cellsState selectorRow selectorColumn
    (cellsAssembly modulus.size (auxiliaryAssembly modulus (auxiliaryRow, oldRow.1)), oldRow.2)
    (cellsAssembly modulus.size (auxiliaryAssembly modulus (auxiliaryColumn, oldColumn.1)),
      oldColumn.2)
  have retained := cells_entry modulus.size auxiliaryState
    (auxiliaryAssembly modulus (auxiliaryRow, oldRow.1), oldRow.2)
    (auxiliaryAssembly modulus (auxiliaryColumn, oldColumn.1), oldColumn.2)
  have prepared := auxiliary_entry modulus state auxiliaryRow auxiliaryColumn oldRow oldColumn
  exact selected.trans (congrArg
    (fun value : ℂ =>
      ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec selectorRow *
        star ((BasisPreparation.zero (selectorLayout modulus.size)).normalized.vec
          selectorColumn)) * value) (retained.trans prepared))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
