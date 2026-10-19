/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.QubitReadouts
public import QuantumAlg.Core.Execution.Context.Layout
public import QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.QubitReadouts
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Gate.Placement.Canonical

/-!
# Physical interface of one teleportation block

Alice's input, Alice's Bell half and Bob's Bell half occupy three distinct
supplied systems in that order [dW19, qcnotes.tex:785,789]. Two actual retained
finite cells receive Alice's measurement results. All five entries remain
live, including both measured quantum systems and both classical results.
-/

namespace QuantumAlg.QuantumTeleportation.Block

noncomputable section

open Execution

/-- Ordered physical systems for the source's three-qubit protocol. -/
@[expose] public def layout : QuantumLayout 3 :=
  (QuantumSignature.qubits 3).canonicalPlacement.layout

/-- The unknown input and both shared Bell halves are supplied quantum interface systems. -/
public def quantumContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addSuppliedLayout ⟨0⟩ layout (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

/-- The fixed execution interface includes two real writable measurement cells. -/
public def context : RuntimeCtx .quantum :=
  MeasurementCells.context quantumContext 2 2

/-- Classical cells do not alter the identity or order of the supplied quantum systems. -/
lemma layout_wires_eq_context : layout.wires = context.quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires, context, MeasurementCells.context_quantumWires]
  change layout.wires = layout.wires ++ []
  exact (List.append_nil _).symm

/-- The corresponding physical positions come from equality of complete wire records. -/
public def position : Fin 3 ≃ Fin context.systemCount :=
  positionsOfEqualWires layout context.quantumLayout layout_wires_eq_context

/-- Every addressed position is the same original dimension-two physical system. -/
lemma position_dimension (index : Fin 3) :
    (context.quantumLayout.wire (position index)).dimension = 2 := by
  rw [position, wireAtCorrespondingPosition]
  rfl

/-- Actual context coordinates expressed in the source's big-endian three-qubit basis. -/
public def binaryBasis : context.register.Index ≃ (Qubits 3).Index :=
  (basisOfEqualWires layout context.quantumLayout layout_wires_eq_context).symm.trans
    (QuantumSignature.qubitsIndexEquiv 3)

/-- Two distinct destinations, each with the real finite binary storage shape. -/
public def resultCell (index : Fin 2) : CWriteRef context (.finite 2) :=
  MeasurementCells.reference quantumContext 2 2 index

/-- Structural read of the two stored outcomes; no result is supplied independently. -/
public def resultInput : CInputRef context (.fixedVector 2 (.finite 2)) :=
  QubitReadouts.input resultCell

/-- Alice measures exactly the original input and her Bell half, in that order. -/
public def readouts : List (ZReadout context) :=
  QubitReadouts.readouts (fun index : Fin 2 => position (index.castLE (by decide)))
    (fun index => position_dimension (index.castLE (by decide))) resultCell

end

end QuantumAlg.QuantumTeleportation.Block
