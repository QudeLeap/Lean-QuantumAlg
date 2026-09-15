/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Assembly
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.State.Preservation
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Actual runtime placement for the full shared frame and arithmetic payload

Fixed auxiliary wires precede the supplied input and payload in runtime
order. The native matrix uses the exact per-wire assembly; physical gate
identities remain unchanged and every payload bit is charged in the live
context. A complete arithmetic body executes after one fixed preparation.
Its full trace, native pool, and depth are retained, and supplied flags
cannot disappear into an uncharged reference [LYL+26, sec_EEA/sub_regshare.tex:16-26].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntime

noncomputable section

open Execution PayloadPreparation

/-- Runtime order is exactly fresh auxiliary wires followed by the unchanged supplied input and
  payload. -/
theorem payloadRuntime_after_physical (width payloadWidth : Nat) :
    (after width payloadWidth).physicalIdx =
      (InputPreparation.auxiliaryLayout width).identities ++ (inputLayout width
        payloadWidth).identities := by
  change ((InputPreparation.auxiliaryLayout width).wires ++ (before width
    payloadWidth).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (InputPreparation.auxiliaryLayout width).identities ++ (before width
    payloadWidth).physicalIdx = _
  rw [PayloadPreparation.before_physical]

private theorem input_subset (width payloadWidth : Nat) :
    (InputPreparation.inputLayout width).identities ⊆ (inputLayout width
      payloadWidth).identities := by
  intro wire present
  change wire ∈ List.ofFn (fun index : Fin width =>
    InputPreparation.prefixWidth width + index.val) at present
  obtain ⟨index, position⟩ := List.mem_ofFn.mp present
  change wire ∈ List.ofFn (fun index : Fin (width + payloadWidth) => physicalIndex width index.val)
  refine List.mem_ofFn.mpr ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  change (if index.val < width then InputPreparation.prefixWidth width + index.val
    else (encoding width).width + (index.val - width)) = wire
  rw [if_pos index.isLt]
  exact position

private theorem original_subset (width payloadWidth : Nat) :
    (InputPreparation.after width).physicalIdx ⊆ (after width payloadWidth).physicalIdx := by
  intro wire present
  rw [InputPreparation.after_physical] at present
  rw [payloadRuntime_after_physical]
  rcases List.mem_append.mp present with auxiliary | input
  · exact List.mem_append.mpr (Or.inl auxiliary)
  · exact List.mem_append.mpr (Or.inr (input_subset width payloadWidth input))

/-- Every native address belongs to the real context, including the supplied payload. -/
theorem payloadRuntime_range_contained (width payloadWidth : Nat) :
    List.range (frameEncoding width payloadWidth).width ⊆ (after width
      payloadWidth).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  change wire < (encoding width).width + payloadWidth at bound
  by_cases original : wire < (encoding width).width
  · exact original_subset width payloadWidth (InputPreparation.range_contained width
      (List.mem_range.mpr original))
  · rw [payloadRuntime_after_physical]
    apply List.mem_append.mpr
    right
    change wire ∈ List.ofFn (fun index : Fin (width + payloadWidth) => physicalIndex width
      index.val)
    let index : Fin (width + payloadWidth) :=
      ⟨width + (wire - (encoding width).width), by omega⟩
    refine List.mem_ofFn.mpr ⟨index, ?_⟩
    change (if width + (wire - (encoding width).width) < width then _
      else (encoding width).width + (width + (wire - (encoding width).width) - width)) = wire
    rw [if_neg (by omega)]
    omega

/-- Place the actual native matrix through its per-wire basis assembly and exact live footprint. -/
def program (width payloadWidth : Nat) (body : UnitaryCircuit (Qubits (frameEncoding width
  payloadWidth).width)) :
    UnitaryCircuit (after width payloadWidth).register :=
  (UnitaryCircuit.reindex (PayloadAssembly.basisEquiv width payloadWidth).symm body).seq
    (UnitaryCircuit.identity (after width payloadWidth).register (after width
      payloadWidth).physicalIdx
      (after width payloadWidth).identitiesNodup)

/-- Every live identity is listed in the actual context order and no native address is dropped. -/
theorem payloadRuntime_program_physical (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding width payloadWidth).width) :
    (program width payloadWidth body).physical_idx = (after width payloadWidth).physicalIdx := by
  change UnitaryCircuit.unionPhysicalIdx body.physical_idx (after width
    payloadWidth).physicalIdx = _
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  exact payloadRuntime_range_contained width payloadWidth (within present)

/-- The runtime matrix is exactly the native matrix on the proved actual basis correspondence. -/
theorem payloadRuntime_program_matrix_entry (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width))
    (row column : (after width payloadWidth).register.Index) :
    (program width payloadWidth body).matrix row column =
      body.matrix (PayloadAssembly.basisEquiv width payloadWidth row)
        (PayloadAssembly.basisEquiv width payloadWidth column) := by
  have matrix : ((program width payloadWidth body).matrix : HilbertOperator (after width
    payloadWidth).register) =
      Matrix.reindex (PayloadAssembly.basisEquiv width payloadWidth).symm
        (PayloadAssembly.basisEquiv width payloadWidth).symm
        (body.matrix : HilbertOperator (Qubits (frameEncoding width payloadWidth).width)) := by
    change (1 : HilbertOperator (after width payloadWidth).register) * _ = _
    exact Matrix.one_mul _
  rw [matrix]
  rfl

/-- A proved native basis action is the same actual runtime action with no phase discarded. -/
theorem payloadRuntime_program_apply_ket (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width))
    (input output : (Qubits (frameEncoding width payloadWidth).width).Index)
    (action : body.applyNormalized (NormalizedVector.ket input) = NormalizedVector.ket output) :
    (program width payloadWidth body).applyNormalized
        (NormalizedVector.ket (R := (after width payloadWidth).register)
          ((PayloadAssembly.basisEquiv width payloadWidth).symm input)) =
      NormalizedVector.ket (R := (after width payloadWidth).register)
        ((PayloadAssembly.basisEquiv width payloadWidth).symm output) := by
  have placed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits (frameEncoding width payloadWidth).width) (S := (after width
      payloadWidth).register)
    (PayloadAssembly.basisEquiv width payloadWidth).symm body input output action
  rw [program, UnitaryCircuit.applyNormalized_seq]
  exact (UnitaryCircuit.applyNormalized_identity (after width payloadWidth).register
    (after width payloadWidth).physicalIdx (after width payloadWidth).identitiesNodup _).trans
      placed

/-- The footprint-completing identity contributes no event to the same actual native trace. -/
theorem payloadRuntime_program_eventTrace (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width)) :
    (program width payloadWidth body).eventTrace = body.eventTrace := by
  have empty : (UnitaryCircuit.identity (after width payloadWidth).register (after width
    payloadWidth).physicalIdx
      (after width payloadWidth).identitiesNodup).eventTrace = [] := rfl
  rw [program, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace,
    empty, List.append_nil]

/-- Actual runtime placement preserves every native-coordinate multiplicity. -/
theorem payloadRuntime_program_eventCost (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width)) :
    (program width payloadWidth body).eventCost = body.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, payloadRuntime_program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Execute the same placed unitary by the one live-context circuit instruction. -/
def circuit (width payloadWidth : Nat) (body : UnitaryCircuit (Qubits (frameEncoding width
  payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding width payloadWidth).width) :
    Circuit (after width payloadWidth) (after width payloadWidth) :=
  .unitary (program width payloadWidth body) (payloadRuntime_program_physical width
    payloadWidth body within)

/-- Every classical block evolves by the same complete operator tensored with the reference. -/
theorem payloadRuntime_circuit_block_matrix (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding width payloadWidth).width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (after width payloadWidth) Reference H) (store : Store (after width
      payloadWidth)) (history : H) :
    (((circuit width payloadWidth body within).execute Reference state).block (store, (history,
      ()))).matrix =
      let operator := UnitaryOperator.prodTensor (program width payloadWidth body).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator (Register.prod (after width payloadWidth).register Reference)) *
        (state.block (store, history)).matrix *
          (operator : HilbertOperator
            (Register.prod (after width payloadWidth).register Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program width payloadWidth body)
    (payloadRuntime_program_physical width payloadWidth body within) store history

/-- Every native duration assignment has the same actual evaluated depth after runtime placement. -/
theorem payloadRuntime_program_depth (width payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding width payloadWidth).width))
    (duration : Resource.Event .quantum → Nat) :
    (program width payloadWidth body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq]
  change (UnitaryCircuit.reindex
    (PayloadAssembly.basisEquiv width payloadWidth).symm body).evaluatedEventDepth duration + 0 = _
  rw [Nat.add_zero]
  simp only [UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.reindex_eventDepth]

/-- One fixed auxiliary preparation followed by the supplied actual complete arithmetic body. -/
def code (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width) :
    Circuit (before modulus.size payloadWidth) (after modulus.size payloadWidth) :=
  .seq (PayloadPreparation.circuit modulus payloadWidth)
    (circuit modulus.size payloadWidth body within)

/-- Exactly one preparation event precedes the entire unchanged actual native trace. -/
theorem payloadRuntime_code_eventTrace (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).eventTrace path =
      (InputPreparation.preparation modulus).event :: body.eventTrace := by
  change [(InputPreparation.preparation modulus).event] ++
    (program modulus.size payloadWidth body).eventTrace = _
  rw [payloadRuntime_program_eventTrace]
  rfl

/-- The actual pool contains one preparation singleton and the same native body pool. -/
theorem payloadRuntime_code_resourcePool (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).resourcePool path =
      ResourcePool.singleton (InputPreparation.preparation modulus).event + body.eventCost := by
  change ResourcePool.ofList _ = _
  rw [payloadRuntime_code_eventTrace, ResourcePool.ofList_cons,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, add_comm]

/-- Actual serial depth charges fixed preparation once for every supplied duration assignment. -/
theorem payloadRuntime_code_depth (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (duration : Resource.Event .quantum → Nat)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).depth duration path =
      duration (InputPreparation.preparation modulus).event + body.evaluatedEventDepth duration
        := by
  change duration (InputPreparation.preparation modulus).event +
    (program modulus.size payloadWidth body).evaluatedEventDepth duration = _
  rw [payloadRuntime_program_depth]

/-- Actual execution visits only the supplied context and the complete prepared context. -/
theorem payloadRuntime_code_visitedContexts (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).visitedContexts path =
      [before modulus.size payloadWidth, after modulus.size payloadWidth,
        after modulus.size payloadWidth] := rfl

private theorem input_le (width payloadWidth : Nat) :
    OwnedQubits.space (width + payloadWidth) ≤
      OwnedQubits.space (frameEncoding width payloadWidth).width := by
  have count : width + payloadWidth ≤ (frameEncoding width payloadWidth).width := by
    have complete := payloadPreparation_total_width width payloadWidth
    omega
  intro axis
  cases axis with
  | classicalBits => exact le_rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then _ else 0) ≤
        if (2 : ℕ+) = dimension then _ else 0
      split_ifs
      · exact count
      · exact le_rfl

/-- Same-execution peak resident space counts every payload bit throughout preparation and body. -/
theorem payloadRuntime_code_resident (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).peakResidentSpace path ≤
      OwnedQubits.space (frameEncoding modulus.size payloadWidth).width := by
  unfold Circuit.peakResidentSpace
  rw [payloadRuntime_code_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil,
    payloadPreparation_after_resident, SpacePool.max_zero, SpacePool.max_self,
    payloadPreparation_before_resident]
  exact SpacePool.max_le (input_le modulus.size payloadWidth) le_rfl

/-- Same-execution peak owned auxiliary space retains all supplied and prepared systems. -/
theorem payloadRuntime_code_auxiliary (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    (path : (code modulus payloadWidth body within).Path) :
    (code modulus payloadWidth body within).peakAuxiliarySpace path ≤
      OwnedQubits.space (frameEncoding modulus.size payloadWidth).width := by
  unfold Circuit.peakAuxiliarySpace
  rw [payloadRuntime_code_visitedContexts]
  simp only [Circuit.peak, List.foldr_cons, List.foldr_nil,
    payloadPreparation_after_auxiliary, SpacePool.max_zero, SpacePool.max_self,
    payloadPreparation_before_auxiliary]
  exact SpacePool.max_le (input_le modulus.size payloadWidth) le_rfl

/-- The actual joint quantum state is prepared once and conjugated by this same complete body. -/
theorem payloadRuntime_code_quantumMarginal (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size payloadWidth) Reference H) :
    ((code modulus payloadWidth body within).execute Reference state).quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (program modulus.size payloadWidth body).matrix
          (1 : UnitaryOperator Reference))
        ((PayloadPreparation.circuit modulus payloadWidth).execute
          Reference state).quantumMarginal := by
  rw [code, Circuit.execute_seq, State.mapHistory_quantumMarginal, circuit,
    Circuit.execute_unitary]
  simp only [State.unitary, ExecutionState.mapClassical_quantumMarginal]
  exact ExecutionState.fixedUnitary_quantumMarginal _ _

/-- Every external reference entry is preserved by actual preparation and local arithmetic. -/
theorem payloadRuntime_code_reference_entry (modulus payloadWidth : Nat)
    (body : UnitaryCircuit (Qubits (frameEncoding modulus.size payloadWidth).width))
    (within : body.physical_idx ⊆ List.range (frameEncoding modulus.size payloadWidth).width)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size payloadWidth) Reference H)
    (left right : Reference.Index) :
    (∑ basis : (after modulus.size payloadWidth).register.Index,
      ((code modulus payloadWidth body within).execute Reference state).quantumMarginal.matrix
        (basis, left) (basis, right)) =
      ∑ basis : (before modulus.size payloadWidth).register.Index,
        state.quantumMarginal.matrix (basis, left) (basis, right) := by
  rw [payloadRuntime_code_quantumMarginal]
  exact (DensityOperator.localUnitary_reference_entry (program modulus.size payloadWidth
    body).matrix
    (((PayloadPreparation.circuit modulus payloadWidth).execute Reference state).quantumMarginal)
      left right).trans
        (Circuit.prepare_reference_entry state auxiliaryKey
          (InputPreparation.auxiliaryLayout modulus.size)
          (payloadPreparation_auxiliary_fresh modulus.size payloadWidth)
          (payloadPreparation_auxiliary_disjoint modulus.size payloadWidth)
          (InputPreparation.preparation modulus) left right)

end

end QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntime
