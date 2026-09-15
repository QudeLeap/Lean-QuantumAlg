/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Reference.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Execute the actual shared-EEA phase kernel on its prepared runtime frame

The physical source order and runtime preparation order are connected by
the previously verified per-wire basis correspondence. This owner reindexes
the actual native phase program through that correspondence and executes it
with the single `Circuit.unitary` constructor. A trailing identity includes
every live system in the footprint and contributes no native event.

The resulting matrix is characterized entry by entry on the complete source
register labels. Actual classical blocks evolve by this same matrix tensored
with the identity on the full external reference. The source phase assignments
are [LYL+26, sec_EEA/sub_regshare.tex:303-305]; their coherent unitary action is
interpreted as in [dW19, qcnotes.tex:5405]. No additional semantic executor,
event declaration, or caller cleanliness premise is introduced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativeRuntime

noncomputable section

open Execution ControlPreparation PreparedFrame

private theorem after_physical (width : Nat) :
    (after width).physicalIdx = bodyWidth width :: List.range (bodyWidth width) := by
  change ((controlLayout width).wires ++ (before width).quantumWires).map QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires, control_identities]
  change [bodyWidth width] ++ (OwnedQubits.context (bodyWidth width)).physicalIdx = _
  rw [OwnedQubits.ownedQubits_physicalIdx]
  rfl

private theorem range_contained (width : Nat) :
    List.range (encoding width).width ⊆ (after width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  have complete := complete_width width
  rw [after_physical]
  by_cases final : wire = bodyWidth width
  · exact List.mem_cons.mpr (Or.inl final)
  · exact List.mem_cons.mpr (Or.inr (List.mem_range.mpr (by omega)))

/-- The original native gates on exactly the post-preparation register coordinates. -/
def program (width : Nat) (enough : 2 ≤ width.size) : UnitaryCircuit (after width).register :=
  UnitaryCircuit.seq
    (UnitaryCircuit.reindex (basisEquiv width).symm (NativeControl.program width enough))
    (UnitaryCircuit.identity (after width).register (after width).physicalIdx
      (after width).identitiesNodup)

/-- Every live physical system is present; the primitive targets retain their source identities. -/
theorem program_placement (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).physical_idx = (after width).physicalIdx := by
  change UnitaryCircuit.unionPhysicalIdx (NativeControl.program width enough).physical_idx
    (after width).physicalIdx = (after width).physicalIdx
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  exact range_contained width
    (EncodedBit.GateSpec.programList_physical_idx_subset_range
      (NativeControl.gates width enough) present)

/-- The unitary matrix follows the exact prepared-frame basis correspondence, entry by entry. -/
theorem program_matrix_entry (width : Nat) (enough : 2 ≤ width.size)
    (row column : (after width).register.Index) :
    (program width enough).matrix row column =
      (NativeControl.program width enough).matrix
        (basisEquiv width row) (basisEquiv width column) := by
  have matrix : ((program width enough).matrix : HilbertOperator (after width).register) =
      Matrix.reindex (basisEquiv width).symm (basisEquiv width).symm
        ((NativeControl.program width enough).matrix :
          HilbertOperator (Qubits (encoding width).width)) := by
    change (1 : HilbertOperator (after width).register) * _ = _
    exact Matrix.one_mul _
  rw [matrix]
  rfl

private theorem realized_entry {Data : Type} [DecidableEq Data]
    (label : BinaryLabelEncoding Data) (body : UnitaryCircuit (Qubits label.width))
    (step : Data → Data) (realizes : UnitaryCircuit.Realizes label body step) (row column : Data) :
    body.matrix (label.encode row) (label.encode column) =
      if row = step column then 1 else 0 := by
  have columnAction := congrArg
    (fun vector : NormalizedVector (Qubits label.width) => vector (label.encode row))
    (realizes.apply_encoded_ket column)
  change body.applyVec (NormalizedVector.ket (R := Qubits label.width) (label.encode column))
      (label.encode row) =
    NormalizedVector.ket (R := Qubits label.width) (label.encode (step column))
      (label.encode row) at columnAction
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] at columnAction
  simpa only [label.encode_injective.eq_iff] using columnAction

/-- The runtime matrix implements the full native register update without a relative-phase gap. -/
theorem program_source_entry (width : Nat) (enough : 2 ≤ width.size)
    (row column : (after width).register.Index) :
    (program width enough).matrix row column =
      if frameEquiv width row = NativeControl.step (frameEquiv width column) then 1 else 0 := by
  rw [program_matrix_entry, ← encode_frameEquiv, ← encode_frameEquiv]
  exact realized_entry (encoding width) (NativeControl.program width enough)
    NativeControl.step (NativeControl.program_realizes width enough) _ _

/-- The actual state update is one native unitary instruction on the complete live context. -/
def circuit (width : Nat) (enough : 2 ≤ width.size) : Circuit (after width) (after width) :=
  .unitary (program width enough) (program_placement width enough)

/-- Internally allocate Ctrl zero, then execute the phase predicate and its inverse cleanup. -/
def initializeThenControl (width : Nat) (enough : 2 ≤ width.size) :
    Circuit (before width) (after width) :=
  .seq (ControlPreparation.circuit width) (circuit width enough)

theorem program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace = (NativeControl.program width enough).eventTrace := by
  have empty : (UnitaryCircuit.identity (after width).register (after width).physicalIdx
      (after width).identitiesNodup).eventTrace = [] := rfl
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace,
    empty, List.append_nil]

theorem program_eventCost (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (NativeControl.program width enough).eventCost := by
  have empty : (UnitaryCircuit.identity (after width).register (after width).physicalIdx
      (after width).identitiesNodup).eventCost = 0 := rfl
  rw [program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.reindex_eventCost, empty, add_zero]

/-- The actual initialization event and both predicate passes stay in the same execution trace. -/
theorem initializeThenControl_trace (width : Nat) (enough : 2 ≤ width.size)
    (path : (initializeThenControl width enough).Path) :
    (initializeThenControl width enough).eventTrace path =
      (preparation width).event :: (NativeControl.program width enough).eventTrace := by
  change [(preparation width).event] ++ (program width enough).eventTrace = _
  rw [program_eventTrace]
  rfl

variable {Reference : Register} {H : Type} [Fintype H]

/-- Actual execution conjugates each complete classical block by this local matrix and IRef. -/
theorem execute_block_matrix (width : Nat) (enough : 2 ≤ width.size)
    (state : State (after width) Reference H) (store : Store (after width)) (history : H) :
    (((circuit width enough).execute Reference state).block (store, (history, ()))).matrix =
      let operator := UnitaryOperator.prodTensor (program width enough).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator (Register.prod (after width).register Reference)) *
        (state.block (store, history)).matrix *
          (operator : HilbertOperator
            (Register.prod (after width).register Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program width enough)
    (program_placement width enough) store history

/-- Every external-reference matrix entry is preserved on arbitrary correlated input states. -/
theorem execute_reference_entry (width : Nat) (enough : 2 ≤ width.size)
    (state : State (after width) Reference H) (left right : Reference.Index) :
    (∑ basis : (after width).register.Index,
      ((circuit width enough).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (after width).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) :=
  Circuit.unitary_reference_entry (program width enough) (program_placement width enough)
    state left right

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativeRuntime
