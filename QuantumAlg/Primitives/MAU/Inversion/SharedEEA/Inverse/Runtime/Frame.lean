/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Assembly
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Actual runtime placement on the complete two-word shared frame

The runtime context stores auxiliary wires followed by the two supplied
words. The native gate addresses retain their original physical values,
which are all proved to occur in that exact context list. The adapter uses
the explicit per-wire basis equivalence and a final identity with the
context's actual ordered footprint; it does not relabel physical wires.

Any actual native program on the same full frame can use this placement,
including the forward and reused inverse in measured division
[LYL+26, sec_point_add/sec_point_add.tex:51-79]. Its native trace and pool are
unchanged. The `Circuit.unitary` constructor remains the single execution
instruction, acting jointly with an arbitrary external reference.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntimeFrame

noncomputable section

open Execution InversePreparation

/-- Runtime order is exactly fresh auxiliary wires followed by the unchanged two supplied words. -/
theorem after_physical (width : Nat) :
    (after width).physicalIdx =
      (InputPreparation.auxiliaryLayout width).identities ++ (inputLayout width).identities := by
  change ((InputPreparation.auxiliaryLayout width).wires ++ (before width).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (InputPreparation.auxiliaryLayout width).identities ++ (before width).physicalIdx = _
  rw [InversePreparation.before_physical]

private theorem input_subset (width : Nat) :
    (InputPreparation.inputLayout width).identities ⊆ (inputLayout width).identities := by
  intro wire present
  change wire ∈ List.ofFn (fun index : Fin width =>
    InputPreparation.prefixWidth width + index.val) at present
  obtain ⟨index, position⟩ := List.mem_ofFn.mp present
  change wire ∈ List.ofFn (fun index : Fin (width + width) => physicalIndex width index.val)
  refine List.mem_ofFn.mpr ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  change (if index.val < width then InputPreparation.prefixWidth width + index.val
    else (encoding width).width + (index.val - width)) = wire
  rw [if_pos index.isLt]
  exact position

private theorem original_subset (width : Nat) :
    (InputPreparation.after width).physicalIdx ⊆ (after width).physicalIdx := by
  intro wire present
  rw [InputPreparation.after_physical] at present
  rw [after_physical]
  rcases List.mem_append.mp present with auxiliary | input
  · exact List.mem_append.mpr (Or.inl auxiliary)
  · exact List.mem_append.mpr (Or.inr (input_subset width input))

/-- Every native address belongs to the real context, including the supplied rightmost word. -/
theorem range_contained (width : Nat) :
    List.range (OutputCopy.encoding width).width ⊆ (after width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  change wire < (encoding width).width + width at bound
  by_cases original : wire < (encoding width).width
  · exact original_subset width (InputPreparation.range_contained width
      (List.mem_range.mpr original))
  · rw [after_physical]
    apply List.mem_append.mpr
    right
    change wire ∈ List.ofFn (fun index : Fin (width + width) => physicalIndex width index.val)
    let index : Fin (width + width) :=
      ⟨width + (wire - (encoding width).width), by omega⟩
    refine List.mem_ofFn.mpr ⟨index, ?_⟩
    change (if width + (wire - (encoding width).width) < width then _
      else (encoding width).width + (width + (wire - (encoding width).width) - width)) = wire
    rw [if_neg (by omega)]
    omega

/-- Place the actual native matrix through its per-wire basis assembly and exact live footprint. -/
def program (width : Nat) (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    UnitaryCircuit (after width).register :=
  (UnitaryCircuit.reindex (InverseAssembly.basisEquiv width).symm body).seq
    (UnitaryCircuit.identity (after width).register (after width).physicalIdx
      (after width).identitiesNodup)

/-- Every live identity is listed in the actual context order and no native address is dropped. -/
theorem program_physical (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width) :
    (program width body).physical_idx = (after width).physicalIdx := by
  change UnitaryCircuit.unionPhysicalIdx body.physical_idx (after width).physicalIdx = _
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  exact range_contained width (within present)

/-- The runtime matrix is exactly the native matrix on the proved actual basis correspondence. -/
theorem program_matrix_entry (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (row column : (after width).register.Index) :
    (program width body).matrix row column =
      body.matrix (InverseAssembly.basisEquiv width row)
        (InverseAssembly.basisEquiv width column) := by
  have matrix : ((program width body).matrix : HilbertOperator (after width).register) =
      Matrix.reindex (InverseAssembly.basisEquiv width).symm
        (InverseAssembly.basisEquiv width).symm
        (body.matrix : HilbertOperator (Qubits (OutputCopy.encoding width).width)) := by
    change (1 : HilbertOperator (after width).register) * _ = _
    exact Matrix.one_mul _
  rw [matrix]
  rfl

/-- A proved native basis action is the same actual runtime action with no phase discarded. -/
theorem program_apply_ket (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (input output : (Qubits (OutputCopy.encoding width).width).Index)
    (action : body.applyNormalized (NormalizedVector.ket input) = NormalizedVector.ket output) :
    (program width body).applyNormalized
        (NormalizedVector.ket (R := (after width).register)
          ((InverseAssembly.basisEquiv width).symm input)) =
      NormalizedVector.ket (R := (after width).register)
        ((InverseAssembly.basisEquiv width).symm output) := by
  have placed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits (OutputCopy.encoding width).width) (S := (after width).register)
    (InverseAssembly.basisEquiv width).symm body input output action
  rw [program, UnitaryCircuit.applyNormalized_seq]
  exact (UnitaryCircuit.applyNormalized_identity (after width).register
    (after width).physicalIdx (after width).identitiesNodup _).trans placed

/-- The footprint-completing identity contributes no event to the same actual native trace. -/
theorem program_eventTrace (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    (program width body).eventTrace = body.eventTrace := by
  have empty : (UnitaryCircuit.identity (after width).register (after width).physicalIdx
      (after width).identitiesNodup).eventTrace = [] := rfl
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace,
    empty, List.append_nil]

/-- Actual runtime placement preserves every native-coordinate multiplicity. -/
theorem program_eventCost (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    (program width body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Execute the same placed unitary by the one live-context circuit instruction. -/
def circuit (width : Nat) (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width) :
    Circuit (after width) (after width) :=
  .unitary (program width body) (program_physical width body within)

/-- Every classical block evolves by the same complete operator tensored with the reference. -/
theorem circuit_block_matrix (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (after width) Reference H) (store : Store (after width)) (history : H) :
    (((circuit width body within).execute Reference state).block (store, (history, ()))).matrix =
      let operator := UnitaryOperator.prodTensor (program width body).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator (Register.prod (after width).register Reference)) *
        (state.block (store, history)).matrix *
          (operator : HilbertOperator
            (Register.prod (after width).register Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program width body)
    (program_physical width body within) store history

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntimeFrame
