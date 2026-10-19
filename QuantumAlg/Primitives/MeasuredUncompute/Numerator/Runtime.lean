/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Values
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime.Frame
import all QuantumAlg.Core.Execution.Selected.Unitary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Native frame gates beside actual stored measurement results

Retaining the finite result cells changes no quantum wire. The native frame
program is placed through the existing complete physical layout and then
transported across those unchanged wires. Both placements preserve the full
operator, native event trace, and external reference correlations.
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorRuntime

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

/-- Retaining classical outcomes leaves the complete ordered physical wire list intact. -/
lemma frame_wires (width : Nat) :
    (InversePreparation.after width).quantumLayout.wires =
      (context width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, RuntimeCtx.quantumLayout_wires]
  exact (MeasurementCells.context_quantumWires (InversePreparation.after width) 2 width).symm

/-- Transport coordinates through the same complete live physical wire records. -/
def frameCoordinates (width : Nat) :
    (InversePreparation.after width).register.Index ≃ (context width).register.Index :=
  basisOfEqualWires (InversePreparation.after width).quantumLayout
    (context width).quantumLayout (frame_wires width)

/-- The physical coordinate transport is the retained-cell coordinate map. -/
lemma frameCoordinates_eq_cells (width : Nat) :
    frameCoordinates width =
      MeasurementCells.basisEquiv (InversePreparation.after width) 2 width := by
  apply Equiv.ext
  intro basis
  funext wire
  obtain ⟨old, rfl⟩ :=
    (MeasurementCells.wireEquiv (InversePreparation.after width) 2 width).surjective wire
  apply Fin.ext
  have samePosition :
      positionsOfEqualWires (InversePreparation.after width).quantumLayout
        (context width).quantumLayout (frame_wires width) old =
          MeasurementCells.wireEquiv (InversePreparation.after width) 2 width old := by
    apply Fin.ext
    exact (MeasurementCells.wireEquiv_val (InversePreparation.after width) 2 width old).symm
  have physical := basisOfEqualWires_value (InversePreparation.after width).quantumLayout
    (context width).quantumLayout (frame_wires width) basis old
  rw [samePosition] at physical
  exact physical.trans
    (MeasurementCells.basisEquiv_value (InversePreparation.after width) 2 width
      basis old).symm

/-- An actual native word acts on the full two-input frame beside retained finite cells. -/
def program (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    UnitaryCircuit AlgorithmGate.model .empty (context width).quantumLayout :=
  unitaryOfEqualWires (InversePreparation.after width).quantumLayout
    (context width).quantumLayout (frame_wires width)
      (InverseRuntimeFrame.program width body)

/-- The exact matrix reads the same physically selected source coordinates. -/
lemma program_matrix (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (row column : (context width).register.Index) :
    ((program width body).matrix environment) row column =
      (body.matrix environment)
        (UnitaryCircuit.basisAt (InverseRuntimeFrame.source width)
          (InversePreparation.after width).quantumLayout
          (InverseRuntimeFrame.position width) (InverseRuntimeFrame.position_dimensions width)
          ((frameCoordinates width).symm row))
        (UnitaryCircuit.basisAt (InverseRuntimeFrame.source width)
          (InversePreparation.after width).quantumLayout
          (InverseRuntimeFrame.position width) (InverseRuntimeFrame.position_dimensions width)
          ((frameCoordinates width).symm column)) := by
  rw [program, unitaryOfEqualWires_matrix]
  exact InverseRuntimeFrame.program_matrix_entry width body
    ((frameCoordinates width).symm row) ((frameCoordinates width).symm column)

/-- Source positions read exactly the existing complete-frame binary label. -/
lemma selected_basis (width : Nat) (basis : (context width).register.Index) :
    UnitaryCircuit.basisAt (InverseRuntimeFrame.source width)
      (InversePreparation.after width).quantumLayout
      (InverseRuntimeFrame.position width) (InverseRuntimeFrame.position_dimensions width)
      ((frameCoordinates width).symm basis) =
        (QubitLayout.canonical (OutputCopy.encoding width).width).basisEquiv.symm
          (frameBasis width basis) := by
  have sameRead :
      UnitaryCircuit.basisAt (InverseRuntimeFrame.source width)
        (InversePreparation.after width).quantumLayout
        (InverseRuntimeFrame.position width) (InverseRuntimeFrame.position_dimensions width)
        ((frameCoordinates width).symm basis) =
      UnitaryCircuit.selectedInput (InverseRuntimeFrame.source width)
        (InversePreparation.after width).quantumLayout
        (InverseRuntimeFrame.position width) (InverseRuntimeFrame.position_dimensions width)
        ((frameCoordinates width).symm basis) := by
    funext index
    apply Fin.ext
    rfl
  rw [sameRead]
  have frame : frameBasis width basis =
      InverseAssembly.basisEquiv width
        ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm basis) :=
    rfl
  rw [frame, frameCoordinates_eq_cells]
  exact InverseRuntimeFrame.selectedBasis_eq_basisEquiv width
    ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm basis)

/-- The same placed matrix is the canonical binary view of the actual native circuit. -/
lemma program_binary_matrix (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (row column : (context width).register.Index) :
    ((program width body).matrix environment) row column =
      (body.binaryMatrix environment) (frameBasis width row) (frameBasis width column) := by
  rw [program_matrix, selected_basis, selected_basis]
  rfl

/-- Classical storage changes no native event in the actual program. -/
lemma program_trace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    (program width body).eventTrace .empty .empty = body.eventTrace .empty .empty := by
  rw [program, unitaryOfEqualWires_trace, InverseRuntimeFrame.program_eventTrace]

/-- The resource pool is the ledger of the same placed native word. -/
lemma program_cost (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    (program width body).eventCost .empty .empty = body.eventCost .empty .empty := by
  rw [program, unitaryOfEqualWires_cost, InverseRuntimeFrame.program_eventCost]

/-- Run the actual placed member with the existing unitary instruction. -/
def code (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width) (context width) allowAllocation :=
  .unitary (program width body)

/-- A retained finite result vector selects its corresponding concrete native member. -/
def selected (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty) (context width) (context width) allowAllocation :=
  .branch (input width) (fun value => code width (body value) allowAllocation)

/-- Each actual store read selects one member on every complete reference block. -/
lemma selected_reference (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {runtimeEnvironment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((selected width body).execute runtimeEnvironment Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((program width (body (entry.1.read (input width)))).matrix runtimeEnvironment.quantum)
        (1 : UnitaryOperator Reference)).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal (input width) (fun value => program width (body value))
    runtimeEnvironment state

end

end QuantumAlg.MeasuredUncompute.NumeratorRuntime
