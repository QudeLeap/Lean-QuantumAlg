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

variable {environment : OracleModel.empty.Interpretation}

private def alignedIncrement (low high extra : Nat) (same : extra + high = low) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bridgeEncoding low high).width).toQuantum :=
  same ▸ placedIncrementProgram extra high

private lemma alignedIncrement_realizes (low high extra : Nat) (same : extra + high = low) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (alignedIncrement low high extra same)
      environment
      bridgeIncrementStep := by
  subst low
  exact hrsPlacedIncrement_realizes extra high

private lemma alignedIncrement_resources (low high extra : Nat) (same : extra + high = low)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (alignedIncrement low high extra same).eventCost =
        (controlledBorrowedIncrementProgram high).eventCost ∧
      (alignedIncrement low high extra same).evaluatedEventDepth assign =
        (controlledBorrowedIncrementProgram high).evaluatedEventDepth assign := by
  subst low
  exact hrsPlacedIncrement_resources extra high assign

private def alignedCarry (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (bridgeEncoding low high).width).toQuantum :=
  same ▸ placedCarryProgram low extra constant

private lemma alignedCarry_realizes (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) :
    UnitaryCircuit.Realizes (bridgeEncoding low high) (alignedCarry low high extra same constant)
      environment
      (bridgeCarryStep (fun input => decide (2 ^ low ≤ input.val + constant.val))) := by
  subst high
  exact hrsPlacedCarry_realizes low extra constant

private lemma alignedCarry_resources (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low))
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (alignedCarry low high extra same constant).eventCost = (carryProgram low constant).eventCost ∧
      (alignedCarry low high extra same constant).evaluatedEventDepth assign =
        (carryProgram low constant).evaluatedEventDepth assign := by
  subst high
  exact hrsPlacedCarry_resources low extra constant assign

private lemma increment_capacity (width : Nat) :
    (lowWidth width - highWidth width) + highWidth width = lowWidth width :=
  Nat.sub_add_cancel (hrsSplit_capacity width).2.1

private lemma carry_capacity (width : Nat) :
    (lowWidth width - 2) + (highWidth width - (lowWidth width - 2)) = highWidth width := by
  have := (hrsSplit_capacity width).1
  omega

/-- Execute the six real blocks on the existing low/high/dirty carrier. -/
def recursiveBridgeProgram (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).toQuantum :=
  let increment := alignedIncrement (lowWidth width) (highWidth width)
    (lowWidth width - highWidth width) (increment_capacity width)
  let complement := controlledComplementProgram (lowWidth width) (highWidth width)
  let carry := alignedCarry (lowWidth width) (highWidth width)
    (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant
  (((((increment.seq complement).seq carry).seq increment).seq carry).seq complement)

/-- Increment the high word by the low carry, restoring arbitrary dirty input exactly. -/
lemma hrsRecursiveBridge_realizes (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    UnitaryCircuit.Realizes (bridgeEncoding (lowWidth width) (highWidth width))
      (recursiveBridgeProgram width constant) environment
      (bridgeOutput (fun input => decide (2 ^ lowWidth width ≤ input.val + constant.val))) := by
  have hi := alignedIncrement_realizes (environment := environment)
    (lowWidth width) (highWidth width)
    (lowWidth width - highWidth width) (increment_capacity width)
  have hj := hrsControlledComplement_realizes (environment := environment)
    (lowWidth width) (highWidth width)
  have hc := alignedCarry_realizes (environment := environment) (lowWidth width) (highWidth width)
    (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant
  exact (((((hi.seq hj).seq hc).seq hi).seq hc).seq hj).congrStep
    (hrsCarryBridge_steps (highWidth width) _)

/-- The bridge uses the exact canonical carrier of the original word and one dirty bit. -/
lemma hrsRecursiveBridge_interface (width : Nat) (_constant : Fin (2 ^ lowWidth width)) :
    (bridgeEncoding (lowWidth width) (highWidth width)).width = width + 1 ∧
      (QubitLayout.canonical
        (bridgeEncoding (lowWidth width) (highWidth width)).width).systemIdx =
          List.range (width + 1) := by
  constructor
  · rw [hrsBridgeEncoding_width, hrsSplit_width_sum]
  · rw [hrsBridgeEncoding_width, hrsSplit_width_sum]
    exact QubitLayout.canonical_systemIdx (width + 1)

/-- Each native coordinate counts the three actual component programs twice. -/
lemma hrsRecursiveBridge_native_count (width : Nat) (constant : Fin (2 ^ lowWidth width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (recursiveBridgeProgram width constant).eventCost =
      2 * (ResourcePool.count focus
          (controlledBorrowedIncrementProgram (highWidth width)).eventCost +
        highWidth width *
          (if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
            then 1 else 0) +
        ResourcePool.count focus (carryProgram (lowWidth width) constant).eventCost) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).1,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).1,
    hrsControlledComplement_native_count]
  omega

/-- The event count follows from the actual component ledgers, including small widths. -/
lemma hrsRecursiveBridge_event_count (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).eventCost.card =
      2 * ((controlledBorrowedIncrementProgram (highWidth width)).eventCost.card +
        highWidth width + (carryProgram (lowWidth width) constant).eventCost.card) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.seq_eventCost, Multiset.card_add]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).1,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).1,
    (hrsControlledComplement_serial_resources (lowWidth width) (highWidth width)).1]
  omega

/-- Unit-duration depth follows the actual serial composition of the six blocks. -/
lemma hrsRecursiveBridge_serial_depth (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).evaluatedEventDepth (fun _ => 1) =
      2 * ((controlledBorrowedIncrementProgram (highWidth width)).evaluatedEventDepth (fun _ => 1) +
        highWidth width +
        (carryProgram (lowWidth width) constant).evaluatedEventDepth (fun _ => 1)) := by
  simp only [recursiveBridgeProgram, UnitaryCircuit.evaluatedEventDepth_seq]
  simp only [(alignedIncrement_resources _ _ _ (increment_capacity width) (fun _ => 1)).2,
    (alignedCarry_resources _ _ _ (carry_capacity width) constant (fun _ => 1)).2,
    (hrsControlledComplement_serial_resources (lowWidth width) (highWidth width)).2]
  omega

private def alignedIncrementGates (low high extra : Nat) (same : extra + high = low) :
    List (EncodedBit.GateSpec (bridgeEncoding low high)) :=
  same ▸ placedIncrementGates extra high

private lemma alignedIncrementGates_step (low high extra : Nat) (same : extra + high = low)
    (state : BridgeRegisters (Fin (2 ^ low)) high) :
    EncodedBit.GateSpec.stepList (alignedIncrementGates low high extra same) state =
      bridgeIncrementStep state := by
  subst low
  exact hrsPlacedIncrementGates_step extra high state

private lemma alignedIncrementGates_events (low high extra : Nat) (same : extra + high = low) :
    (alignedIncrementGates low high extra same).map (EncodedBit.GateSpec.event .empty) =
      (alignedIncrement low high extra same).eventTrace := by
  subst low
  exact (EncodedBit.GateSpec.programList_eventTrace (QubitLayout.canonical _) .empty
    (placedIncrementGates extra high)).symm

private def alignedCarryGates (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) : List (EncodedBit.GateSpec (bridgeEncoding low high)) :=
  same ▸ placedCarryGates low extra constant

private lemma alignedCarryGates_step (low high extra : Nat) (same : (low - 2) + extra = high)
    (constant : Fin (2 ^ low)) (state : BridgeRegisters (Fin (2 ^ low)) high) :
    EncodedBit.GateSpec.stepList (alignedCarryGates low high extra same constant) state =
      bridgeCarryStep (fun input => decide (2 ^ low ≤ input.val + constant.val)) state := by
  subst high
  exact hrsPlacedCarryGates_step low extra constant state

private lemma alignedCarryGates_events (low high extra : Nat)
    (same : (low - 2) + extra = high) (constant : Fin (2 ^ low)) :
    (alignedCarryGates low high extra same constant).map (EncodedBit.GateSpec.event .empty) =
      (alignedCarry low high extra same constant).eventTrace := by
  subst high
  exact (EncodedBit.GateSpec.programList_eventTrace (QubitLayout.canonical _) .empty
    (placedCarryGates low extra constant)).symm

/-- The exact six bridge blocks retained as native instructions for further control lowering. -/
def recursiveBridgeGates (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    List (EncodedBit.GateSpec (bridgeEncoding (lowWidth width) (highWidth width))) :=
  carryBridgeGates
    (alignedIncrementGates (lowWidth width) (highWidth width)
      (lowWidth width - highWidth width) (increment_capacity width))
    (controlledComplementGates (lowWidth width) (highWidth width))
    (alignedCarryGates (lowWidth width) (highWidth width)
      (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant)

/-- The explicit shared-layout bridge list has the same exact arithmetic action. -/
lemma hrsRecursiveBridgeGates_step (width : Nat) (constant : Fin (2 ^ lowWidth width))
    (state : BridgeRegisters (Fin (2 ^ lowWidth width)) (highWidth width)) :
    EncodedBit.GateSpec.stepList (recursiveBridgeGates width constant) state =
      bridgeOutput (fun input => decide (2 ^ lowWidth width ≤ input.val + constant.val)) state :=
  hrsCarryBridge_step _ _ _ _
    (alignedIncrementGates_step (lowWidth width) (highWidth width)
      (lowWidth width - highWidth width) (increment_capacity width))
    (hrsControlledComplement_step (lowWidth width) (highWidth width))
    (alignedCarryGates_step (lowWidth width) (highWidth width)
      (highWidth width - (lowWidth width - 2)) (carry_capacity width) constant) state

/-- Every source gate remains in its original order, with no relabelled or omitted native event. -/
lemma hrsRecursiveBridgeGates_events (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeGates width constant).map (EncodedBit.GateSpec.event .empty) =
      (recursiveBridgeProgram width constant).eventTrace := by
  simp only [recursiveBridgeGates, carryBridgeGates, List.map_append,
    alignedIncrementGates_events, alignedCarryGates_events,
    recursiveBridgeProgram, UnitaryCircuit.seq_eventTrace,
    controlledComplementProgram, EncodedBit.GateSpec.programList_eventTrace, List.append_assoc]

/-- The literal list has the already proved native event cardinality of the source construction. -/
lemma hrsRecursiveBridgeGates_length (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeGates width constant).length =
      (recursiveBridgeProgram width constant).eventCost.card := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, ← hrsRecursiveBridgeGates_events]
  simp [ResourcePool.ofList]

end

end QuantumAlg.MAU.Addition.HRS
