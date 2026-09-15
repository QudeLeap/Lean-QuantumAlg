/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import all QuantumAlg.Primitives.MAU.Addition.HRS.IncrementPlacement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.Complement
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Actual six-block HRS bridge on the recursive split

The low and high widths are the ceiling and floor halves of the original
word. Proven capacity equalities place the real increment and carry
programs on those existing halves. Six actual sequential blocks remove
the initial dirty-control value [HRS16, paper.tex:224-226,232-260].
The word and its one dirty bit are the entire interface, including the
zero-width and one-width cases. Full constant addition still requires the
two recursive half additions after this bridge.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

private def alignedIncrement (low high extra : Nat) (same : extra + high = low) :
    UnitaryCircuit (Qubits (bridgeEncoding low high).width) :=
  same ▸ placedIncrementProgram extra high

private theorem alignedIncrement_realizes (low high extra : Nat) (same : extra + high = low) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (alignedIncrement low high extra same)
      bridgeIncrementStep := by
  subst low
  exact hrsPlacedIncrement_realizes extra high

private theorem alignedIncrement_resources (low high extra : Nat) (same : extra + high = low)
    (assign : Resource.Event .quantum → Nat) :
    (alignedIncrement low high extra same).eventCost =
        (controlledBorrowedIncrementProgram high).eventCost ∧
      (alignedIncrement low high extra same).evaluatedEventDepth assign =
        (controlledBorrowedIncrementProgram high).evaluatedEventDepth assign := by
  subst low
  exact hrsPlacedIncrement_resources extra high assign

private theorem alignedIncrement_range (low high extra : Nat) (same : extra + high = low) :
    (alignedIncrement low high extra same).physical_idx ⊆ List.range (low + high + 1) := by
  subst low
  exact hrsPlacedIncrement_physical_range extra high

private def alignedCarry (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) : UnitaryCircuit (Qubits (bridgeEncoding low high).width) :=
  same ▸ placedCarryProgram low extra constant

private theorem alignedCarry_realizes (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (alignedCarry low high extra same constant)
      (bridgeCarryStep (fun input => decide (2 ^ low ≤ input.val + constant.val))) := by
  subst high
  exact hrsPlacedCarry_realizes low extra constant

private theorem alignedCarry_resources (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) (assign : Resource.Event .quantum → Nat) :
    (alignedCarry low high extra same constant).eventCost = (carryProgram low constant).eventCost ∧
      (alignedCarry low high extra same constant).evaluatedEventDepth assign =
        (carryProgram low constant).evaluatedEventDepth assign := by
  subst high
  exact hrsPlacedCarry_resources low extra constant assign

private theorem alignedCarry_range (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) :
    (alignedCarry low high extra same constant).physical_idx ⊆ List.range (low + high + 1) := by
  subst high
  exact hrsPlacedCarry_physical_range low extra constant

private theorem increment_capacity (width : Nat) :
    (lowWidth width - highWidth width) + highWidth width = lowWidth width :=
  Nat.sub_add_cancel (hrsSplit_capacity width).2.1

private theorem carry_capacity (width : Nat) :
    (lowWidth width - 2) + (highWidth width - (lowWidth width - 2)) = highWidth width := by
  have := (hrsSplit_capacity width).1
  omega

/-- Execute the six real blocks on the existing low/high/dirty carrier. -/
def recursiveBridgeProgram (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    UnitaryCircuit (Qubits (bridgeEncoding (lowWidth width) (highWidth width)).width) :=
  let increment := alignedIncrement (lowWidth width) (highWidth width)
    (lowWidth width - highWidth width) (increment_capacity width)
  let complement := controlledComplementProgram (lowWidth width) (highWidth width)
  let carry := alignedCarry (lowWidth width) (highWidth width)
    (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant
  (((((increment.seq complement).seq carry).seq increment).seq carry).seq complement)

/-- Increment the high word by the low carry, restoring arbitrary dirty input exactly. -/
theorem hrsRecursiveBridge_realizes (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    UnitaryCircuit.Realizes (bridgeEncoding (lowWidth width) (highWidth width))
      (recursiveBridgeProgram width constant)
      (bridgeOutput (fun input => decide (2 ^ lowWidth width ≤ input.val + constant.val))) := by
  have hi := alignedIncrement_realizes (lowWidth width) (highWidth width)
    (lowWidth width - highWidth width) (increment_capacity width)
  have hj := hrsControlledComplement_realizes (lowWidth width) (highWidth width)
  have hc := alignedCarry_realizes (lowWidth width) (highWidth width)
    (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant
  exact (((((hi.seq hj).seq hc).seq hi).seq hc).seq hj).congrStep
    (hrsCarryBridge_steps (highWidth width) _)

/-- Every actual bridge operation stays in the original word and one dirty bit. -/
theorem hrsRecursiveBridge_interface (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (bridgeEncoding (lowWidth width) (highWidth width)).width = width + 1 ∧
      (recursiveBridgeProgram width constant).physical_idx ⊆ List.range (width + 1) := by
  constructor
  · rw [hrsBridgeEncoding_width, hrsSplit_width_sum]
  · have hi := alignedIncrement_range (lowWidth width) (highWidth width)
      (lowWidth width - highWidth width) (increment_capacity width)
    have hj : (controlledComplementProgram (lowWidth width) (highWidth width)).physical_idx ⊆
        List.range (lowWidth width + highWidth width + 1) :=
      EncodedBit.GateSpec.programList_physical_idx_subset_range
        (controlledComplementGates (lowWidth width) (highWidth width))
    have hc := alignedCarry_range (lowWidth width) (highWidth width)
      (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant
    have h := UnitaryCircuit.seq_physical_idx_subset _ _
      (UnitaryCircuit.seq_physical_idx_subset _ _
        (UnitaryCircuit.seq_physical_idx_subset _ _
          (UnitaryCircuit.seq_physical_idx_subset _ _
            (UnitaryCircuit.seq_physical_idx_subset _ _ hi hj) hc) hi) hc) hj
    unfold recursiveBridgeProgram
    simpa only [hrsSplit_width_sum] using h

/-- Each native coordinate counts the three actual component programs twice. -/
theorem hrsRecursiveBridge_native_count (width : Nat) (constant : Fin (2 ^ lowWidth width))
    (focus : Resource.Event .quantum) :
    ResourcePool.count focus (recursiveBridgeProgram width constant).eventCost =
      2 * (ResourcePool.count focus
          (controlledBorrowedIncrementProgram (highWidth width)).eventCost +
        highWidth width *
          (if (.gate (.builtin "cnot") : Resource.Event .quantum) = focus then 1 else 0) +
        ResourcePool.count focus (carryProgram (lowWidth width) constant).eventCost) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).1,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).1,
    hrsControlledComplement_native_count]
  omega

/-- The event count follows from the actual component ledgers, including small widths. -/
theorem hrsRecursiveBridge_event_count (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).eventCost.card =
      2 * ((controlledBorrowedIncrementProgram (highWidth width)).eventCost.card +
        highWidth width + (carryProgram (lowWidth width) constant).eventCost.card) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.seq_eventCost, Multiset.card_add]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).1,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).1,
    (hrsControlledComplement_serial_resources (lowWidth width) (highWidth width)).1]
  omega

/-- Unit-duration depth follows the actual serial composition of the six blocks. -/
theorem hrsRecursiveBridge_serial_depth (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).evaluatedEventDepth (fun _ => 1) =
      2 * ((controlledBorrowedIncrementProgram (highWidth width)).evaluatedEventDepth (fun _ => 1) +
        highWidth width +
        (carryProgram (lowWidth width) constant).evaluatedEventDepth (fun _ => 1)) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).2,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).2,
    (hrsControlledComplement_serial_resources (lowWidth width) (highWidth width)).2]
  omega

end

end QuantumAlg.MAU.Addition.HRS
