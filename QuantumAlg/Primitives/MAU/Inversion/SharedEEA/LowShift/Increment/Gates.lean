/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Increment
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Gates

/-!
# Literal HRS instructions on the original low shift wires

The proved borrowed-word width equality transports the actual HRS list.
Product lifting and complete placement preserve every spectator and dirty
Work1 bit, including the zero-width counter case.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement

noncomputable section

open EncodedBit GateSpec LowShiftRegisters

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
    List (GateSpec (Addition.HRS.bridgeEncoding (width + 3) (width.size))) :=
  castBridgeGates (extra_add_length width)
    (Addition.HRS.placedIncrementGates (extra width) (width.size))

private theorem focusedGates_step (width : Nat)
    (state : Addition.HRS.BridgeRegisters (Fin (2 ^ (width + 3))) (width.size)) :
    stepList (focusedGates width) state = Addition.HRS.bridgeIncrementStep state :=
  castBridgeGates_step (extra_add_length width) _
    (Addition.HRS.hrsPlacedIncrementGates_step (extra width) (width.size)) state

private theorem focusedGates_trace (width : Nat) :
    (focusedGates width).map (event .empty) =
      (Addition.HRS.placedIncrementGates (extra width) (width.size)).map
        (event .empty) :=
  castBridgeGates_trace (extra_add_length width) _

/-- Lift every original instruction past all original spectator fields. -/
private def groupedGates (width : Nat) :
    List (GateSpec (BinaryLabelEncoding.prod
      (Addition.HRS.bridgeEncoding (width + 3) (width.size))
      (LowShiftPlacement.remainderEncoding width))) :=
  (focusedGates width).map (GateSpec.prodLeft (LowShiftPlacement.remainderEncoding width))

/-- The literal native list at the established complete original physical placement. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  (groupedGates width).map (LowShiftPlacement.placement width).placeGate

/-- Every full input frame follows the original finite increment, with arbitrary work restored. -/
theorem lowShiftIncrement_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state = step state := by
  have lifted := stepList_prodLeft
    (left := Addition.HRS.bridgeEncoding (width + 3) (width.size))
    (LowShiftPlacement.remainderEncoding width) (focusedGates width)
    ((LowShiftPlacement.placement width).grouping state)
  have grouped : stepList (groupedGates width)
      ((LowShiftPlacement.placement width).grouping state) =
      (Addition.HRS.bridgeIncrementStep
        ((LowShiftPlacement.placement width).grouping state).1,
        ((LowShiftPlacement.placement width).grouping state).2) :=
    lifted.trans (congrArg
      (fun value => (value, ((LowShiftPlacement.placement width).grouping state).2))
      (focusedGates_step width ((LowShiftPlacement.placement width).grouping state).1))
  have placed : (LowShiftPlacement.placement width).grouping.symm
      (Addition.HRS.bridgeIncrementStep
        ((LowShiftPlacement.placement width).grouping state).1,
        ((LowShiftPlacement.placement width).grouping state).2) = step state := by
    simpa only [LowShiftPlacement.placement_grouping_eq, LowShiftPlacement.placedStep]
      using placed_step width state
  exact ((LowShiftPlacement.placement width).placeGates_step
    (groupedGates width) state).trans
      ((congrArg (LowShiftPlacement.placement width).grouping.symm grouped).trans placed)

/-- The emitted native word preserves all amplitudes and relative phases on the complete frame. -/
theorem lowShiftIncrement_gates_realizes (width : Nat)
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width)
      (programList layout .empty (gates width)) step :=
  realizesList_congrStep layout .empty _ (lowShiftIncrement_gates_step width)

/-- Width transport, product lifting and full placement retain the original instruction order. -/
theorem lowShiftIncrement_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace := by
  have placed : (gates width).map (event .empty) =
      (groupedGates width).map (event .empty) := by
    exact (programList_eventTrace (QubitLayout.canonical _) .empty
      (gates width)).symm.trans
        ((LowShiftPlacement.placement width).placeGates_eventTrace
          (QubitLayout.canonical _) .empty (groupedGates width))
  have lifted := map_event_prodLeft (oracles := .empty)
    (left := Addition.HRS.bridgeEncoding (width + 3) (width.size))
    (LowShiftPlacement.remainderEncoding width) (focusedGates width)
  have original := (programList_eventTrace (QubitLayout.canonical _) .empty
    (Addition.HRS.placedIncrementGates (extra width) (width.size))).symm
  exact placed.trans (lifted.trans ((focusedGates_trace width).trans
    (original.trans (program_eventTrace width).symm)))

/-- The complete native multiplicity pool is unchanged in every gate coordinate. -/
theorem lowShiftIncrement_gates_eventCost (width : Nat) :
    ResourcePool.ofList ((gates width).map (event .empty)) = (program width).eventCost := by
  rw [lowShiftIncrement_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The exact HRS count retains the zero-width counter and every borrowed-work instruction. -/
theorem lowShiftIncrement_gates_length (width : Nat) :
    (gates width).length =
      4 * width.size + 20 * (width.size - 1) + 4 * (width.size - 2) := by
  have count := congrArg Multiset.card (lowShiftIncrement_gates_eventCost width)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at count
  have originalCost : (program width).eventCost =
      (Addition.HRS.placedIncrementProgram (extra width) (width.size)).eventCost :=
    (UnitaryCircuit.ofList_eventTrace_eq_eventCost (program width)).symm.trans
      ((congrArg ResourcePool.ofList (program_eventTrace width)).trans
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost
          (Addition.HRS.placedIncrementProgram (extra width) (width.size))))
  have nativeCost := (Addition.HRS.hrsPlacedIncrement_resources
    (extra width) (width.size) (fun _ => 1)).1
  exact count.trans ((congrArg Multiset.card originalCost).trans
    ((congrArg Multiset.card nativeCost).trans
      (Addition.HRS.hrsControlledBorrowedIncrement_event_count (width.size))))

end

end QuantumAlg.MAU.Inversion.SharedEEA.LowShiftIncrement
