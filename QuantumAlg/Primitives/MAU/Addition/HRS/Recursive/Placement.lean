/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Base
import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Layout
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting
import all QuantumAlg.Components.Encoded.BitGates.Realization
import Mathlib.Tactic.Ring

/-!
# Reuse the one dirty bit across the two recursive HRS calls

Each child circuit acts on its own word and the same final dirty bit.
Its sibling word is an untouched tensor factor [HRS16, paper.tex:232-260].
These placements use the existing physical insertion and tensor operations;
the high-call index cast only changes parentheses in the big-endian label.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- Insert the inactive high word before the low child's dirty bit. -/
def placeLowChild (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding low).width)) :
    UnitaryCircuit (Qubits (bridgeEncoding low high).width) :=
  UnitaryCircuit.insertMiddle (leftWidth := low) (middleWidth := high) (rightWidth := 1) program

/-- The low recursive call preserves the high word and restores the shared dirty bit. -/
theorem hrsPlaceLowChild_realizes (low high : Nat) (constant : Fin (2 ^ low))
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding low).width))
    (h : UnitaryCircuit.Realizes (oneDirtyEncoding low) program (oneDirtyOutput constant)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (placeLowChild low high program)
      (fun state => ((addWord constant state.1.1, state.1.2), state.2)) := by
  exact UnitaryCircuit.Realizes.insertMiddle
    (left := BinaryLabelEncoding.finIdentity low)
    (middle := BinaryLabelEncoding.finIdentity high) (right := BinaryLabelEncoding.bool) h

theorem hrsPlaceLowChild_range (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding low).width))
    (contained : program.physical_idx ⊆ List.range (low + 1)) :
    (placeLowChild low high program).physical_idx ⊆ List.range (low + high + 1) :=
  UnitaryCircuit.insertMiddle_physical_idx_subset_range
    (leftWidth := low) (middleWidth := high) (rightWidth := 1) program contained

/-- Adding the inactive sibling changes neither the native ledger nor the evaluated depth. -/
theorem hrsPlaceLowChild_resources (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding low).width))
    (assign : Resource.Event .quantum → Nat) :
    (placeLowChild low high program).eventCost = program.eventCost ∧
      (placeLowChild low high program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign :=
  ⟨UnitaryCircuit.insertMiddle_eventCost
      (leftWidth := low) (middleWidth := high) (rightWidth := 1) program,
    UnitaryCircuit.insertMiddle_evaluatedEventDepth
      (leftWidth := low) (middleWidth := high) (rightWidth := 1) assign program⟩

/-- Reassociate the unchanged low/high/dirty basis label. -/
def highChildIndex (low high : Nat) :
    Fin (2 ^ (low + (high + 1))) ≃ Fin (2 ^ (low + high + 1)) :=
  finCongr (congrArg (fun width : Nat => 2 ^ width) (Nat.add_assoc low high 1).symm)

theorem hrsHighChildIndex_encode (low high : Nat)
    (lowWord : Fin (2 ^ low)) (highWord : Fin (2 ^ high)) (dirty : Bool) :
    highChildIndex low high
        (prodEquiv (lowWord, (oneDirtyEncoding high).encode (highWord, dirty))) =
      (bridgeEncoding low high).encode ((lowWord, highWord), dirty) := by
  apply Fin.ext
  change (BinaryLabelEncoding.bool.encode dirty).val + 2 ^ 1 * highWord.val +
      2 ^ (high + 1) * lowWord.val =
    (BinaryLabelEncoding.bool.encode dirty).val +
      2 ^ 1 * (highWord.val + 2 ^ high * lowWord.val)
  simp only [pow_add, pow_one]
  ring

/-- Run the actual high child after the untouched low word. -/
def placeHighChild (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding high).width)) :
    UnitaryCircuit (Qubits (bridgeEncoding low high).width) :=
  UnitaryCircuit.reindex (highChildIndex low high) (UnitaryCircuit.prodRight (m := low) program)

/-- The high recursive call preserves the low word and restores the shared dirty bit. -/
theorem hrsPlaceHighChild_realizes (low high : Nat) (constant : Fin (2 ^ high))
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding high).width))
    (h : UnitaryCircuit.Realizes (oneDirtyEncoding high) program (oneDirtyOutput constant)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (placeHighChild low high program)
      (fun state => ((state.1.1, addWord constant state.1.2), state.2)) where
  apply_encoded_ket := by
    rintro ⟨⟨lowWord, highWord⟩, dirty⟩
    have hextended := (h.prodRight (left := BinaryLabelEncoding.finIdentity low)).apply_encoded_ket
      (lowWord, (highWord, dirty))
    have hplaced := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (low + (high + 1))) (S := Qubits (low + high + 1))
      (highChildIndex low high) (UnitaryCircuit.prodRight (m := low) program) _ _ hextended
    change (placeHighChild low high program).applyNormalized
        (NormalizedVector.ket (R := Qubits (low + high + 1)) (highChildIndex low high
          (prodEquiv (lowWord, (oneDirtyEncoding high).encode (highWord, dirty))))) =
      NormalizedVector.ket (R := Qubits (low + high + 1)) (highChildIndex low high
        (prodEquiv (lowWord, (oneDirtyEncoding high).encode
          (addWord constant highWord, dirty)))) at hplaced
    rw [hrsHighChildIndex_encode, hrsHighChildIndex_encode] at hplaced
    change (placeHighChild low high program).applyNormalized
        (NormalizedVector.ket (R := Qubits (low + high + 1))
          ((bridgeEncoding low high).encode ((lowWord, highWord), dirty))) =
      NormalizedVector.ket (R := Qubits (low + high + 1))
        ((bridgeEncoding low high).encode ((lowWord, addWord constant highWord), dirty))
    exact hplaced

theorem hrsPlaceHighChild_range (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding high).width))
    (contained : program.physical_idx ⊆ List.range (high + 1)) :
    (placeHighChild low high program).physical_idx ⊆ List.range (low + high + 1) := by
  have h := UnitaryCircuit.prodRight_physical_idx_subset_range (m := low) program contained
  intro index hindex
  have hlt := List.mem_range.mp (h hindex)
  change index < low + (high + 1) at hlt
  apply List.mem_range.mpr
  omega

theorem hrsPlaceHighChild_resources (low high : Nat)
    (program : UnitaryCircuit (Qubits (oneDirtyEncoding high).width))
    (assign : Resource.Event .quantum → Nat) :
    (placeHighChild low high program).eventCost = program.eventCost ∧
      (placeHighChild low high program).evaluatedEventDepth assign =
        program.evaluatedEventDepth assign := by
  constructor
  · change (UnitaryCircuit.prodRight (m := low) program).eventCost = _
    exact UnitaryCircuit.prodRight_eventCost _
  · change (UnitaryCircuit.prodRight (m := low) program).evaluatedEventDepth assign = _
    exact UnitaryCircuit.prodRight_evaluatedEventDepth assign _

end

end QuantumAlg.MAU.Addition.HRS
