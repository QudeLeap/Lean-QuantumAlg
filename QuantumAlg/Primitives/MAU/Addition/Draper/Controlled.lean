/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Draper.Resources
import all QuantumAlg.Components.Encoded.BitGates.Control
import all QuantumAlg.Core.Base.Depth.EventCount

/-!
# Exact coherently controlled constant addition

The circuit adds one leading quantum control to the literal Draper program.
The control is preserved, and the target receives the modular constant exactly
on its true branch. The basis equality is exact, so the coherent control does
not acquire an unaccounted relative phase. Classical constants remain circuit
parameters [D00, paper.tex:302,352-361].

Each original gate receives its actual additional control coordinate, including
the QFT rotations that already have a control. The shared control serializes
the gate occurrences, and the exact depth follows from that actual schedule
and the same native event ledger.
-/

namespace QuantumAlg.MAU.Addition.Draper

noncomputable section

/-- A leading Boolean control and the complete target word. -/
def controlledEncoding (n : Nat) : BinaryLabelEncoding (Bool × Fin (2 ^ n)) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool (BinaryLabelEncoding.finIdentity n)

/-- Preserve the control and add the compiled constant exactly on its true branch. -/
def controlledOutput {n : Nat} (constant : Nat) (state : Bool × Fin (2 ^ n)) :
    Bool × Fin (2 ^ n) :=
  (state.1, if state.1 then additionOutput constant state.2 else state.2)

/-- The existing checked control constructor shifts the body away from its new leading wire. -/
def controlledProgram (n constant : Nat) : UnitaryCircuit (Qubits (1 + n)) :=
  UnitaryCircuit.controlLeading (additionProgram n constant)

/-- The actual coherent control realizes the exact conditional arithmetic endpoint. -/
theorem draperControlledAddition_realizes (n constant : Nat) :
    UnitaryCircuit.Realizes (controlledEncoding n) (controlledProgram n constant)
      (controlledOutput constant) := by
  have hshift : UnitaryCircuit.Realizes (BinaryLabelEncoding.finIdentity n)
      (UnitaryCircuit.shiftPhysicalIdx 1 (additionProgram n constant))
      (additionOutput constant) := by
    refine ⟨?_⟩
    intro input
    rw [UnitaryCircuit.shiftPhysicalIdx_applyNormalized]
    exact (draperAddition_realizes n constant).apply_encoded_ket input
  have hcontrol := hshift.controlOnTrue [0]
    (UnitaryCircuit.leadingControlLayout (additionProgram n constant))
  apply hcontrol.congrStep
  rintro ⟨control, input⟩
  cases control <;> rfl

/-- The independent output preserves the control value on both branches. -/
@[simp] theorem draperControlledAddition_control (n constant : Nat)
    (state : Bool × Fin (2 ^ n)) :
    (controlledOutput constant state).1 = state.1 := rfl

/-- The full native event ledger is the actual additional-control transform of the body. -/
theorem draperControlledAddition_eventCost (n constant : Nat) :
    (controlledProgram n constant).eventCost =
      ResourcePool.controlForDimension 2 (additionProgram n constant).eventCost := by
  rw [controlledProgram, UnitaryCircuit.controlLeading_eventCost]

/-- The native ledger retains all three gate families with one additional quantum control. -/
theorem draperControlledAddition_native_ledger (n constant : Nat) :
    (controlledProgram n constant).eventCost =
      (2 * n) • ResourcePool.singleton
          ((Resource.Event.gate (.builtin "hadamard")).controlForDimension 2) +
        (2 * n.choose 2) • ResourcePool.singleton
          ((Resource.Event.gate qftControlledPhaseLabel).controlForDimension 2) +
        n • ResourcePool.singleton
          ((Resource.Event.gate
            (.declared "QuantumAlg.Components.Gate" "phase")).controlForDimension 2) := by
  rw [draperControlledAddition_eventCost, draperAddition_eventCost]
  simp [ResourcePool.controlForDimension, Resource.Event.controlForDimension]

/-- Every controlled native coordinate has exactly its corresponding original multiplicity. -/
theorem draperControlledAddition_native_count (n constant : Nat)
    (focus : Resource.Event .quantum) :
    ResourcePool.count (focus.controlForDimension 2) (controlledProgram n constant).eventCost =
      ResourcePool.count focus (additionProgram n constant).eventCost := by
  rw [draperControlledAddition_eventCost, ResourcePool.count_controlForDimension]

/-- The actual controlled-Hadamard count is `2n`. -/
theorem draperControlledAddition_hadamard_count (n constant : Nat) :
    ResourcePool.count ((Resource.Event.gate (.builtin "hadamard")).controlForDimension 2)
      (controlledProgram n constant).eventCost = 2 * n := by
  rw [draperControlledAddition_native_count, draperAddition_hadamard_count]

/-- The existing QFT controlled phases receive a second control, preserving their count. -/
theorem draperControlledAddition_double_phase_count (n constant : Nat) :
    ResourcePool.count ((Resource.Event.gate qftControlledPhaseLabel).controlForDimension 2)
      (controlledProgram n constant).eventCost = n * (n - 1) := by
  rw [draperControlledAddition_native_count, draperAddition_controlled_phase_count]

/-- The `n` compiled-constant phases become native controlled one-qubit phases. -/
theorem draperControlledAddition_phase_count (n constant : Nat) :
    ResourcePool.count
        ((Resource.Event.gate
          (.declared "QuantumAlg.Components.Gate" "phase")).controlForDimension 2)
      (controlledProgram n constant).eventCost = n := by
  rw [draperControlledAddition_native_count, draperAddition_phase_count]

/-- Adding the actual control does not change the number of native gate occurrences. -/
theorem draperControlledAddition_event_count (n constant : Nat) :
    (controlledProgram n constant).eventCost.card = n ^ 2 + 2 * n := by
  rw [draperControlledAddition_eventCost]
  simp only [ResourcePool.controlForDimension, ResourcePool.controlForDimensions,
    Multiset.card_map, draperAddition_event_count]

/-- The controlled circuit occupies the target word and one distinct control wire. -/
@[simp] theorem draperControlledAddition_physical_idx (n constant : Nat) :
    (controlledProgram n constant).physical_idx = List.range (n + 1) := by
  change [0] ++ (UnitaryCircuit.shiftPhysicalIdx 1 (additionProgram n constant)).physical_idx = _
  rw [UnitaryCircuit.shiftPhysicalIdx_physical_idx, draperAddition_physical_idx]
  change 0 :: List.map (fun index => 1 + index) (List.range n) = List.range (n + 1)
  simpa only [Nat.one_add] using (List.range_succ_eq_map (n := n)).symm

/-- Even at target width zero the explicit control remains a live interface wire. -/
theorem draperControlledAddition_qubit_count (n constant : Nat) :
    (controlledEncoding n).width = n + 1 ∧
      (controlledProgram n constant).physical_idx.length = n + 1 := by
  constructor
  · change 1 + n = n + 1
    omega
  · rw [draperControlledAddition_physical_idx, List.length_range]

/-- The shared control serializes every native event, giving exactly `n^2+2n` unit steps. -/
theorem draperControlledAddition_unit_depth (n constant : Nat) :
    (controlledProgram n constant).evaluatedEventDepth (fun _ => 1) =
      n ^ 2 + 2 * n := by
  rw [controlledProgram, UnitaryCircuit.controlLeading,
    UnitaryCircuit.evaluatedEventDepth_controlQubitsAt,
    UnitaryCircuit.shiftPhysicalIdx_eventDepth, DepthExpr.unitCost_eq_eventPool_card]
  change (additionProgram n constant).resourcesFromEventDepth.card = _
  rw [UnitaryCircuit.resourcesFromEventDepth_eq_eventCost, draperAddition_event_count]

end

end QuantumAlg.MAU.Addition.Draper
