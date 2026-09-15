/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Return the HRS recursive split to the original word interface

The exact split/join equivalence restores the original big-endian word
order, and the matching physical block permutation fixes the one external
dirty bit [HRS16, paper.tex:232-260]. The final zero-event identity declares
all wires of this same carrier, including idle wires; it allocates no new
qubits and changes neither the circuit action nor its resource ledger.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- Join the two actual word fields while preserving the last dirty basis bit. -/
def joinIndex (width : Nat) :
    Fin (2 ^ (lowWidth width + highWidth width + 1)) ≃ Fin (2 ^ (width + 1)) where
  toFun label :=
    let source := (prodEquiv (m := lowWidth width + highWidth width) (n := 1)).symm label
    let words := (prodEquiv (m := lowWidth width) (n := highWidth width)).symm source.1
    prodEquiv (joinWord width words, source.2)
  invFun label :=
    let source := (prodEquiv (m := width) (n := 1)).symm label
    prodEquiv (prodEquiv ((splitWord width) source.1), source.2)
  left_inv := by intro label; simp [joinWord]
  right_inv := by intro label; simp [joinWord]

theorem hrsJoinIndex_encode (width : Nat)
    (state : BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width)) :
    joinIndex width ((bridgeEncoding (lowWidth width) (highWidth width)).encode state) =
      (oneDirtyEncoding width).encode (joinWord width state.1, state.2) := by
  change joinIndex width
      (prodEquiv (prodEquiv state.1, BinaryLabelEncoding.bool.encode state.2)) =
    prodEquiv (joinWord width state.1, BinaryLabelEncoding.bool.encode state.2)
  simp only [joinIndex, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  rfl

/-- Apply the exact register-order change to an actual shared-layout circuit. -/
def joinProgram (width : Nat)
    (program : UnitaryCircuit
      (Qubits (bridgeEncoding (lowWidth width) (highWidth width)).width)) :
    UnitaryCircuit (Qubits (oneDirtyEncoding width).width) :=
  let transported := UnitaryCircuit.reindex (joinIndex width) program
  UnitaryCircuit.relabel transported
    { toFun := joinWire width
      map_layout := rfl
      old_nodup := transported.physical_idx_nodup
      new_nodup := transported.physical_idx_nodup.map (hrsJoinWire_injective width) }

/-- Exact action transported through the explicit register split and join. -/
theorem hrsJoinProgram_realizes (width : Nat)
    (program : UnitaryCircuit
      (Qubits (bridgeEncoding (lowWidth width) (highWidth width)).width))
    (step : BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width) →
      BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width))
    (h : UnitaryCircuit.Realizes (bridgeEncoding (lowWidth width) (highWidth width)) program step) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width) (joinProgram width program)
      (fun state =>
        let output := step ((splitWord width) state.1, state.2)
        (joinWord width output.1, output.2)) where
  apply_encoded_ket := by
    rintro ⟨input, dirty⟩
    have hrun := h.apply_encoded_ket ((splitWord width) input, dirty)
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (lowWidth width + highWidth width + 1)) (S := Qubits (width + 1))
      (joinIndex width) program _ _ hrun
    change (UnitaryCircuit.reindex (joinIndex width) program).applyNormalized
        (NormalizedVector.ket (R := Qubits (width + 1)) (joinIndex width
          ((bridgeEncoding (lowWidth width) (highWidth width)).encode
            ((splitWord width) input, dirty)))) =
      NormalizedVector.ket (R := Qubits (width + 1)) (joinIndex width
        ((bridgeEncoding (lowWidth width) (highWidth width)).encode
          (step ((splitWord width) input, dirty)))) at hplaced
    rw [hrsJoinIndex_encode, hrsJoinIndex_encode, hrsJoin_split] at hplaced
    change (joinProgram width program).applyNormalized
        (NormalizedVector.ket (R := Qubits (width + 1))
          ((oneDirtyEncoding width).encode (input, dirty))) =
      NormalizedVector.ket (R := Qubits (width + 1))
        ((oneDirtyEncoding width).encode
          (joinWord width (step ((splitWord width) input, dirty)).1,
            (step ((splitWord width) input, dirty)).2))
    unfold joinProgram
    dsimp only
    exact (UnitaryCircuit.Realizes.applyNormalized_relabel
      (R := Qubits (width + 1))
      (UnitaryCircuit.reindex
        (R := Qubits (lowWidth width + highWidth width + 1)) (S := Qubits (width + 1))
        (joinIndex width) program) _ _).trans hplaced

theorem hrsJoinProgram_range (width : Nat)
    (program : UnitaryCircuit
      (Qubits (bridgeEncoding (lowWidth width) (highWidth width)).width))
    (contained : program.physical_idx ⊆ List.range (width + 1)) :
    (joinProgram width program).physical_idx ⊆ List.range (width + 1) := by
  intro index hindex
  change index ∈ List.map (joinWire width) program.physical_idx at hindex
  rcases List.mem_map.mp hindex with ⟨source, hsource, rfl⟩
  exact List.mem_range.mpr (hrsJoinWire_lt width source (List.mem_range.mp (contained hsource)))

theorem hrsJoinProgram_resources (width : Nat)
    (program : UnitaryCircuit
      (Qubits (bridgeEncoding (lowWidth width) (highWidth width)).width))
    (assign : Resource.Event .quantum → Nat) :
    (joinProgram width program).eventCost = program.eventCost ∧
      (joinProgram width program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  constructor
  · unfold joinProgram
    rw [UnitaryCircuit.relabel_eventCost]
    rfl
  · unfold joinProgram
    rw [UnitaryCircuit.evaluatedEventDepth_relabel]
    rfl

/-- Declare the full existing word/dirty carrier with a zero-event identity. -/
def declareOneDirtyLayout (width : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding width).width)) :
    UnitaryCircuit (Qubits (oneDirtyEncoding width).width) :=
  program.seq (UnitaryCircuit.identity (Qubits (oneDirtyEncoding width).width)
    (List.range (width + 1)) List.nodup_range)

/-- The declared final physical list is exact, including idle carrier wires. -/
theorem hrsDeclareOneDirtyLayout_physical (width : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding width).width))
    (contained : program.physical_idx ⊆ List.range (width + 1)) :
    (declareOneDirtyLayout width program).physical_idx = List.range (width + 1) := by
  change program.physical_idx ∪ List.range (width + 1) = List.range (width + 1)
  exact List.Subset.union_eq_right contained

theorem hrsDeclareOneDirtyLayout_realizes (width : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding width).width))
    (step : OneDirtyRegisters width → OneDirtyRegisters width)
    (h : UnitaryCircuit.Realizes (oneDirtyEncoding width) program step) :
    UnitaryCircuit.Realizes (oneDirtyEncoding width) (declareOneDirtyLayout width program) step :=
  h.seq (UnitaryCircuit.Realizes.identityAt (oneDirtyEncoding width)
    (List.range (width + 1)) List.nodup_range)

theorem hrsDeclareOneDirtyLayout_resources (width : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding width).width))
    (assign : Resource.Event .quantum → Nat) :
    (declareOneDirtyLayout width program).eventCost = program.eventCost ∧
      (declareOneDirtyLayout width program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  constructor
  · simp only [declareOneDirtyLayout, UnitaryCircuit.seq_eventCost,
      UnitaryCircuit.identity_eventCost, add_zero]
  · rw [declareOneDirtyLayout, UnitaryCircuit.evaluatedEventDepth_seq]
    change program.evaluatedEventDepth assign + 0 = program.evaluatedEventDepth assign
    omega

end

end QuantumAlg.MAU.Addition.HRS
