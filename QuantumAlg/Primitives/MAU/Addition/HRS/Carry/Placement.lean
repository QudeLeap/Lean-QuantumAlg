/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.WorkLayout

/-!
# Place the HRS carry inside the inactive high word

The high word contains `low - 2` internally borrowed bits followed by
`extra` unused bits. The actual carry program is extended by an identity
on those unused bits. An explicit block permutation moves its dirty output
past the high word to the final shared wire [HRS16, paper.tex:232-260].
Both the basis permutation and the physical relabeling describe this same
low/dirty/borrowed/unused to low/borrowed/unused/dirty order change.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

private def sharedLabelEquiv (low high : Nat) :
    BridgeRegisters (Fin (2 ^ low)) high ≃ Fin (2 ^ (low + high + 1)) :=
  (Equiv.prodCongr (prodEquiv (m := low) (n := high)) finTwoEquiv.symm).trans
    (prodEquiv (m := low + high) (n := 1))

private theorem sharedLabelEquiv_encode (low high : Nat)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    sharedLabelEquiv low high state = (bridgeEncoding low high).encode state := by
  rcases state with ⟨words, dirty⟩
  cases dirty <;> rfl

/-- Move the packed carry output after the borrowed and unused high-word fields. -/
def carryPlacementIndex (low extra : Nat) :
    Fin (2 ^ ((low + (low - 2 + 1)) + extra)) ≃
      Fin (2 ^ (low + ((low - 2) + extra) + 1)) where
  toFun label :=
    let source := (prodEquiv (m := low + (low - 2 + 1)) (n := extra)).symm label
    let inputWork := (prodEquiv (m := low) (n := low - 2 + 1)).symm source.1
    let work := (carryWorkEquiv low).symm inputWork.2
    sharedLabelEquiv low ((low - 2) + extra)
      ((inputWork.1, prodEquiv (work.1, source.2)), work.2)
  invFun label :=
    let state := (sharedLabelEquiv low ((low - 2) + extra)).symm label
    let high := (prodEquiv (m := low - 2) (n := extra)).symm state.1.2
    prodEquiv (prodEquiv (state.1.1, carryWorkEquiv low (high.1, state.2)), high.2)
  left_inv := by
    intro label
    simp
  right_inv := by
    intro label
    simp

theorem hrsCarryPlacementIndex_encode (low extra : Nat) (input : Fin (2 ^ low))
    (borrowed : Fin (2 ^ (low - 2))) (unused : Fin (2 ^ extra)) (dirty : Bool) :
    carryPlacementIndex low extra
        (prodEquiv ((carryEncoding low).encode
          (input, carryWorkEquiv low (borrowed, dirty)), unused)) =
      (bridgeEncoding low ((low - 2) + extra)).encode
        ((input, prodEquiv (borrowed, unused)), dirty) := by
  change carryPlacementIndex low extra
    (prodEquiv (prodEquiv (input, carryWorkEquiv low (borrowed, dirty)), unused)) = _
  simp only [carryPlacementIndex, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  exact sharedLabelEquiv_encode low ((low - 2) + extra) _

/-- Rotate the source dirty wire past the existing high-word bits. -/
def carryPlacementWire (low extra wire : Nat) : Nat :=
  if wire < low then wire
  else if wire = low then low + (low - 2) + extra
  else if wire < low + (low - 2) + extra + 1 then wire - 1 else wire

private def inverseCarryPlacementWire (low extra wire : Nat) : Nat :=
  if wire < low then wire
  else if wire < low + (low - 2) + extra then wire + 1
  else if wire = low + (low - 2) + extra then low else wire

private theorem carryPlacementWire_left_inverse (low extra wire : Nat) :
    inverseCarryPlacementWire low extra (carryPlacementWire low extra wire) = wire := by
  unfold inverseCarryPlacementWire carryPlacementWire
  split_ifs <;> omega

/-- No two source wires are identified by the physical order change. -/
theorem hrsCarryPlacementWire_injective (low extra : Nat) :
    Function.Injective (carryPlacementWire low extra) := by
  intro a b h
  have h' := congrArg (inverseCarryPlacementWire low extra) h
  simpa only [carryPlacementWire_left_inverse] using h'

theorem hrsCarryPlacementWire_range (low extra wire : Nat)
    (h : wire < low + (low - 2) + extra + 1) :
    carryPlacementWire low extra wire < low + (low - 2) + extra + 1 := by
  unfold carryPlacementWire
  split_ifs <;> omega

/-- Place the actual carry program, retaining its original gate list and internal borrowing. -/
def placedCarryProgram (low extra : Nat) (constant : Fin (2 ^ low)) :
    UnitaryCircuit (Qubits (bridgeEncoding low ((low - 2) + extra)).width) :=
  let transported := UnitaryCircuit.reindex (carryPlacementIndex low extra)
    (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant))
  UnitaryCircuit.relabel transported
    { toFun := carryPlacementWire low extra
      map_layout := rfl
      old_nodup := transported.physical_idx_nodup
      new_nodup := transported.physical_idx_nodup.map
        (hrsCarryPlacementWire_injective low extra) }

/-- The placed carry toggles the final dirty bit and restores the entire low and high words. -/
theorem hrsPlacedCarry_realizes (low extra : Nat) (constant : Fin (2 ^ low)) :
    UnitaryCircuit.Realizes (bridgeEncoding low ((low - 2) + extra))
      (placedCarryProgram low extra constant)
      (bridgeCarryStep (fun input : Fin (2 ^ low) =>
        decide (2 ^ low ≤ input.val + constant.val))) where
  apply_encoded_ket := by
    rintro ⟨⟨input, high⟩, dirty⟩
    obtain ⟨⟨borrowed, unused⟩, rfl⟩ :=
      (prodEquiv (m := low - 2) (n := extra)).surjective high
    have hcarry := hrsCarry_packed_apply low constant input borrowed dirty
    have hextended := UnitaryCircuit.Realizes.prodLeft_applyNormalized_encoded_ket_of_eq
      (carryEncoding low) (BinaryLabelEncoding.finIdentity extra)
      (carryProgram low constant)
      (input, carryWorkEquiv low (borrowed, dirty))
      (input, carryWorkEquiv low
        (borrowed, dirty ^^ decide (2 ^ low ≤ input.val + constant.val))) unused hcarry
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits ((low + (low - 2 + 1)) + extra))
      (S := Qubits (low + ((low - 2) + extra) + 1))
      (carryPlacementIndex low extra)
      (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant)) _ _ hextended
    change (UnitaryCircuit.reindex (carryPlacementIndex low extra)
        (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant))).applyNormalized
        (NormalizedVector.ket (R := Qubits (low + ((low - 2) + extra) + 1))
          (carryPlacementIndex low extra
            (prodEquiv ((carryEncoding low).encode
              (input, carryWorkEquiv low (borrowed, dirty)), unused)))) =
      NormalizedVector.ket (R := Qubits (low + ((low - 2) + extra) + 1))
        (carryPlacementIndex low extra
          (prodEquiv ((carryEncoding low).encode (input, carryWorkEquiv low
            (borrowed, dirty ^^ decide (2 ^ low ≤ input.val + constant.val))), unused))) at hplaced
    rw [hrsCarryPlacementIndex_encode, hrsCarryPlacementIndex_encode] at hplaced
    change (placedCarryProgram low extra constant).applyNormalized
        (NormalizedVector.ket (R := Qubits (low + ((low - 2) + extra) + 1))
          ((bridgeEncoding low ((low - 2) + extra)).encode
            ((input, prodEquiv (borrowed, unused)), dirty))) =
      NormalizedVector.ket (R := Qubits (low + ((low - 2) + extra) + 1))
        ((bridgeEncoding low ((low - 2) + extra)).encode
          ((input, prodEquiv (borrowed, unused)),
            dirty ^^ decide (2 ^ low ≤ input.val + constant.val)))
    unfold placedCarryProgram
    dsimp only
    exact (UnitaryCircuit.Realizes.applyNormalized_relabel
      (R := Qubits (low + ((low - 2) + extra) + 1))
      (UnitaryCircuit.reindex
        (R := Qubits ((low + (low - 2 + 1)) + extra))
        (S := Qubits (low + ((low - 2) + extra) + 1))
        (carryPlacementIndex low extra)
        (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant))) _ _).trans hplaced

/-- The placed carry accesses only the existing halves and their one dirty bit. -/
theorem hrsPlacedCarry_physical_range (low extra : Nat) (constant : Fin (2 ^ low)) :
    (placedCarryProgram low extra constant).physical_idx ⊆
      List.range (low + ((low - 2) + extra) + 1) := by
  have hextended := UnitaryCircuit.prodLeft_physical_idx_subset_range
    (n := extra) (carryProgram low constant)
    (EncodedBit.GateSpec.programList_physical_idx_subset_range (carryGates low constant))
  intro index hindex
  change index ∈ List.map (carryPlacementWire low extra)
    (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant)).physical_idx at hindex
  rcases List.mem_map.mp hindex with ⟨source, hsource, rfl⟩
  have hlt := List.mem_range.mp (hextended hsource)
  have hsource' : source < low + (low - 2) + extra + 1 := by
    change source < (low + (low - 2 + 1)) + extra at hlt
    omega
  have hplaced := hrsCarryPlacementWire_range low extra source hsource'
  apply List.mem_range.mpr
  omega

/-- Identity extension and exact placement retain the carry's literal resource ledger. -/
theorem hrsPlacedCarry_resources (low extra : Nat) (constant : Fin (2 ^ low))
    (assign : Resource.Event .quantum → Nat) :
    (placedCarryProgram low extra constant).eventCost = (carryProgram low constant).eventCost ∧
      (placedCarryProgram low extra constant).evaluatedEventDepth assign =
        (carryProgram low constant).evaluatedEventDepth assign := by
  constructor
  · unfold placedCarryProgram
    rw [UnitaryCircuit.relabel_eventCost]
    change (UnitaryCircuit.prodLeft (n := extra) (carryProgram low constant)).eventCost = _
    exact UnitaryCircuit.prodLeft_eventCost _
  · unfold placedCarryProgram
    rw [UnitaryCircuit.evaluatedEventDepth_relabel]
    change (UnitaryCircuit.prodLeft (n := extra)
      (carryProgram low constant)).evaluatedEventDepth assign = _
    exact UnitaryCircuit.prodLeft_evaluatedEventDepth assign _

end

end QuantumAlg.MAU.Addition.HRS
