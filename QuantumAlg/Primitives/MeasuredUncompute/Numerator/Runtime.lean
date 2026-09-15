/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Values
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Runtime.Frame
import all QuantumAlg.Core.Execution.Selected.Unitary

/-!
# Native frame gates beside actual stored measurement results

Retaining the finite result cells changes no quantum wire. The actual
native frame program therefore uses the same runtime placement through the
classical extension, with every physical identity, native event and matrix
entry preserved. This adapter is shared by the selected numerator reset,
the reused inverse EEA, and the measured product correction
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorRuntime

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

/-- The same native program acts on the complete actual frame beside its retained finite cells. -/
def program (width : Nat) (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    UnitaryCircuit (context width).register :=
  UnitaryCircuit.reindex (MeasurementCells.basisEquiv (InversePreparation.after width) 2 width)
    (InverseRuntimeFrame.program width body)

/-- Runtime placement lists the whole actual live frame in its original order. -/
theorem program_physical (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width) :
    (program width body).physical_idx = (context width).physicalIdx :=
  (InverseRuntimeFrame.program_physical width body within).trans (context_physical width).symm

/-- The actual matrix uses precisely the same per-wire binary frame correspondence. -/
theorem program_matrix (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (row column : (context width).register.Index) :
    (program width body).matrix row column =
      body.matrix (frameBasis width row) (frameBasis width column) :=
  InverseRuntimeFrame.program_matrix_entry width body
    ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm row)
    ((MeasurementCells.basisEquiv (InversePreparation.after width) 2 width).symm column)

/-- Classical storage changes no native event in the actual program. -/
theorem program_trace (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    (program width body).eventTrace = body.eventTrace :=
  (UnitaryCircuit.reindex_eventTrace _ _).trans
    (InverseRuntimeFrame.program_eventTrace width body)

/-- The coordinate pool is the projection of that identical actual native trace. -/
theorem program_cost (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    (program width body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Execute the actual placed member with the existing unitary instruction. -/
def code (width : Nat) (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width) :
    Circuit (context width) (context width) :=
  .unitary (program width body) (program_physical width body within)

/-- A retained finite result vector selects only its corresponding concrete native member. -/
def selected (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : ∀ value, (body value).physical_idx ⊆ List.range (OutputCopy.encoding width).width) :
    Circuit (context width) (context width) :=
  .branch (input width) (fun value => code width (body value) (within value))

/-- Actual store reads select the same member on every classical and full reference block. -/
theorem selected_reference (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : ∀ value, (body value).physical_idx ⊆ List.range (OutputCopy.encoding width).width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) :
    ((selected width body within).execute Reference state).quantumMarginal =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (program width (body (entry.1.read (input width)))).matrix
        (1 : UnitaryOperator Reference)).quantumMarginal :=
  Circuit.selectedUnitary_quantumMarginal (input width) (fun value => program width (body value))
    (fun value => program_physical width (body value) (within value)) state

end

end QuantumAlg.MeasuredUncompute.NumeratorRuntime
