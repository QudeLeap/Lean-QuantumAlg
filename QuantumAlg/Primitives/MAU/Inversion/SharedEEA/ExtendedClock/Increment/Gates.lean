/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Increment
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal HRS instructions on the original extended-clock wires

The borrowed-word equality transports the original HRS instruction list,
including every physical wire. Product lifting retains the entire complement,
and the established complete placement puts those same instructions on Work2,
the two existing high clock bits, the low shift, and Phase2. The complete state
action, ordered trace and exact native count remain those of the original
incrementer. No value restriction is imposed on its borrowed or retained bits.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockIncrement

noncomputable section

open EncodedBit GateSpec ExtendedClockRegisters

/-- Equality transport retains each original instruction and its existing wire addresses. -/
private def castBridgeGates {low target high : Nat} (same : low = target)
    (instructions : List (GateSpec (Addition.HRS.bridgeEncoding low high))) :
    List (GateSpec (Addition.HRS.bridgeEncoding target high)) :=
  same ▸ instructions

private theorem castBridgeGates_step {low target high : Nat} (same : low = target)
    (instructions : List (GateSpec (Addition.HRS.bridgeEncoding low high)))
    (action : ∀ state, stepList instructions state = Addition.HRS.bridgeIncrementStep state)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ target)) high) :
    stepList (castBridgeGates same instructions) state =
      Addition.HRS.bridgeIncrementStep state := by
  cases same
  exact action state

private theorem castBridgeGates_trace {low target high : Nat} (same : low = target)
    (instructions : List (GateSpec (Addition.HRS.bridgeEncoding low high))) :
    (castBridgeGates same instructions).map (event .empty) =
      instructions.map (event .empty) := by
  cases same
  rfl

/-- The actual HRS list after the proved equality of its complete borrowed-word width. -/
private def focusedGates (width : Nat) :
    List (GateSpec (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))) :=
  castBridgeGates (extra_add_clockWidth width)
    (Addition.HRS.placedIncrementGates (extra width) (clockWidth width))

private theorem focusedGates_step (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (clockWidth width)) :
    stepList (focusedGates width) state = Addition.HRS.bridgeIncrementStep state :=
  castBridgeGates_step (extra_add_clockWidth width) _
    (Addition.HRS.hrsPlacedIncrementGates_step (extra width) (clockWidth width)) state

private theorem focusedGates_trace (width : Nat) :
    (focusedGates width).map (event .empty) =
      (Addition.HRS.placedIncrementGates (extra width) (clockWidth width)).map
        (event .empty) :=
  castBridgeGates_trace (extra_add_clockWidth width) _

/-- Lift every original instruction past all original spectator fields. -/
private def groupedGates (width : Nat) :
    List (GateSpec (BinaryLabelEncoding.prod
      (Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
      (ExtendedClockPlacement.remainderEncoding width))) :=
  (focusedGates width).map (GateSpec.prodLeft (ExtendedClockPlacement.remainderEncoding width))

/-- The literal native list at the established complete original physical placement. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  (groupedGates width).map (ExtendedClockPlacement.placement width).placeGate

/-- Every full input frame follows the original finite increment, with arbitrary work restored. -/
theorem extendedClockIncrement_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state = step state := by
  have lifted := stepList_prodLeft
    (left := Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
    (ExtendedClockPlacement.remainderEncoding width) (focusedGates width)
    ((ExtendedClockPlacement.placement width).grouping state)
  have grouped : stepList (groupedGates width)
      ((ExtendedClockPlacement.placement width).grouping state) =
      (Addition.HRS.bridgeIncrementStep
        ((ExtendedClockPlacement.placement width).grouping state).1,
        ((ExtendedClockPlacement.placement width).grouping state).2) :=
    lifted.trans (congrArg
      (fun value => (value, ((ExtendedClockPlacement.placement width).grouping state).2))
      (focusedGates_step width ((ExtendedClockPlacement.placement width).grouping state).1))
  have placed : (ExtendedClockPlacement.placement width).grouping.symm
      (Addition.HRS.bridgeIncrementStep
        ((ExtendedClockPlacement.placement width).grouping state).1,
        ((ExtendedClockPlacement.placement width).grouping state).2) = step state := by
    simpa only [ExtendedClockPlacement.placement_grouping_eq] using placed_step width state
  exact ((ExtendedClockPlacement.placement width).placeGates_step
    (groupedGates width) state).trans
      ((congrArg (ExtendedClockPlacement.placement width).grouping.symm grouped).trans placed)

/-- The emitted native word preserves all amplitudes and relative phases on the complete frame. -/
theorem extendedClockIncrement_gates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates width)) step :=
  realizesList_congrStep layout .empty _ (extendedClockIncrement_gates_step width)

/-- Width transport, product lifting and full placement retain the original instruction order. -/
theorem extendedClockIncrement_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace := by
  have placed : (gates width).map (event .empty) =
      (groupedGates width).map (event .empty) := by
    exact (programList_eventTrace (QubitLayout.canonical _) .empty
      (gates width)).symm.trans
        ((ExtendedClockPlacement.placement width).placeGates_eventTrace
          (QubitLayout.canonical _) .empty (groupedGates width))
  have lifted := map_event_prodLeft (oracles := .empty)
    (left := Addition.HRS.bridgeEncoding (width + 3) (clockWidth width))
    (ExtendedClockPlacement.remainderEncoding width) (focusedGates width)
  have original := (programList_eventTrace (QubitLayout.canonical _) .empty
    (Addition.HRS.placedIncrementGates (extra width) (clockWidth width))).symm
  exact placed.trans (lifted.trans ((focusedGates_trace width).trans
    (original.trans (program_eventTrace width).symm)))

/-- The complete native multiplicity pool is unchanged in every gate coordinate. -/
theorem extendedClockIncrement_gates_eventCost (width : Nat) :
    ResourcePool.ofList ((gates width).map (event .empty)) = (program width).eventCost := by
  rw [extendedClockIncrement_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The exact HRS count includes every instruction on both original high clock bits. -/
theorem extendedClockIncrement_gates_length (width : Nat) :
    (gates width).length =
      4 * (2 + width.size) + 20 * ((2 + width.size) - 1) +
        4 * ((2 + width.size) - 2) := by
  have count := congrArg Multiset.card (extendedClockIncrement_gates_eventCost width)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at count
  have originalCost : (program width).eventCost =
      (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width)).eventCost :=
    (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program width)).symm.trans
      ((congrArg ResourcePool.ofList (program_eventTrace width)).trans
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost
          (Addition.HRS.placedIncrementProgram (extra width) (clockWidth width))))
  have nativeCost := (Addition.HRS.hrsPlacedIncrement_resources
    (extra width) (clockWidth width) (fun _ => 1)).1
  exact count.trans ((congrArg Multiset.card originalCost).trans
    ((congrArg Multiset.card nativeCost).trans
      (Addition.HRS.hrsControlledBorrowedIncrement_event_count (clockWidth width))))

end

end QuantumAlg.MAU.Inversion.SharedEEA.ExtendedClockIncrement
