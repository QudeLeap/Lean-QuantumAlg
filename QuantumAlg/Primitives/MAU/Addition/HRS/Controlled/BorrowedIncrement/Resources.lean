/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement

/-!
# Native resources of the HRS controlled borrowed incrementer

The actual lowering maps X to one CNOT, CNOT to one Toffoli, and Toffoli
to four Toffolis with an internally borrowed wire. The formulas below
count that executed lowering. They do not assert the different controlled
adder cost estimate in the source [HRS16, paper.tex:219-224,245].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

open EncodedBit.GateSpec

private theorem gate_weight (n : Nat) (gate : EncodedBit.GateSpec (TTK.encoding n))
    (weight : Resource.Event .quantum → Nat) :
    ((controlledBorrowedGate n gate).map fun emitted => weight emitted.event).sum =
      gate.xMultiplicity * weight (.gate (.builtin "cnot")) +
        gate.cnotMultiplicity * weight (.gate (.builtin "toffoli")) +
        gate.toffoliMultiplicity * (4 * weight (.gate (.builtin "toffoli"))) := by
  cases gate with
  | x target =>
      simp [controlledBorrowedGate, xMultiplicity, cnotMultiplicity,
        toffoliMultiplicity, eventMultiplicity, event, Resource.GateLabel.builtin]
  | cnot source target hst =>
      simp [controlledBorrowedGate, xMultiplicity, cnotMultiplicity,
        toffoliMultiplicity, eventMultiplicity, event, Resource.GateLabel.builtin]
  | toffoli a b target hab hat hbt =>
      dsimp only [controlledBorrowedGate, controlledOperandToffoli]
      rw [hrsDirtyControlledToffoli_weight]
      simp [xMultiplicity, cnotMultiplicity, toffoliMultiplicity,
        eventMultiplicity, event, Resource.GateLabel.builtin]

private theorem list_weight (n : Nat) (gates : List (EncodedBit.GateSpec (TTK.encoding n)))
    (weight : Resource.Event .quantum → Nat) :
    ((controlledBorrowedList n gates).map fun gate => weight gate.event).sum =
      (gates.map xMultiplicity).sum * weight (.gate (.builtin "cnot")) +
        (gates.map cnotMultiplicity).sum * weight (.gate (.builtin "toffoli")) +
        (gates.map toffoliMultiplicity).sum * (4 * weight (.gate (.builtin "toffoli"))) := by
  induction gates with
  | nil => simp [controlledBorrowedList]
  | cons gate rest ih =>
      change (((controlledBorrowedGate n gate) ++ controlledBorrowedList n rest).map
        fun emitted => weight emitted.event).sum = _
      rw [List.map_append, List.sum_append, gate_weight, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

private theorem increment_weight (n : Nat) (weight : Resource.Event .quantum → Nat) :
    ((controlledBorrowedIncrementGates n).map fun gate => weight gate.event).sum =
      (2 * n) * weight (.gate (.builtin "cnot")) +
        (2 * n + 20 * (n - 1) + 4 * (n - 2)) * weight (.gate (.builtin "toffoli")) := by
  have h := list_weight n (borrowedIncrementGates n) weight
  rw [← programList_x_count_eq_sum, ← programList_cnot_count_eq_sum,
    ← programList_toffoli_count_eq_sum] at h
  change ((controlledBorrowedIncrementGates n).map fun gate => weight gate.event).sum =
      ResourcePool.count (.gate (.builtin "x")) (borrowedIncrementProgram n).eventCost *
          weight (.gate (.builtin "cnot")) +
        ResourcePool.count (.gate (.builtin "cnot")) (borrowedIncrementProgram n).eventCost *
          weight (.gate (.builtin "toffoli")) +
        ResourcePool.count (.gate (.builtin "toffoli")) (borrowedIncrementProgram n).eventCost *
          (4 * weight (.gate (.builtin "toffoli"))) at h
  rw [hrsBorrowedIncrement_x_count, hrsBorrowedIncrement_cnot_count,
    hrsBorrowedIncrement_toffoli_count] at h
  rw [h]
  ring

/-- Every native event coordinate comes from the actual controlled expansion. -/
theorem hrsControlledBorrowedIncrement_native_count (n : Nat)
    (focus : Resource.Event .quantum) :
    ResourcePool.count focus (controlledBorrowedIncrementProgram n).eventCost =
      (2 * n) *
        (if (.gate (.builtin "cnot") : Resource.Event .quantum) = focus then 1 else 0) +
      (2 * n + 20 * (n - 1) + 4 * (n - 2)) *
        (if (.gate (.builtin "toffoli") : Resource.Event .quantum) = focus then 1 else 0) := by
  rw [controlledBorrowedIncrementProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact increment_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- No uncontrolled X leaf remains in the controlled program. -/
theorem hrsControlledBorrowedIncrement_x_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "x")) (controlledBorrowedIncrementProgram n).eventCost =
      0 := by
  simpa [Resource.GateLabel.builtin] using
    hrsControlledBorrowedIncrement_native_count n (.gate (.builtin "x"))

/-- Each borrowed-word complement contributes one CNOT per bit. -/
theorem hrsControlledBorrowedIncrement_cnot_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (controlledBorrowedIncrementProgram n).eventCost = 2 * n := by
  simpa [Resource.GateLabel.builtin] using
    hrsControlledBorrowedIncrement_native_count n (.gate (.builtin "cnot"))

/-- Every original CNOT contributes one Toffoli and every original Toffoli four. -/
theorem hrsControlledBorrowedIncrement_toffoli_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (controlledBorrowedIncrementProgram n).eventCost =
      2 * n + 20 * (n - 1) + 4 * (n - 2) := by
  simpa [Resource.GateLabel.builtin] using
    hrsControlledBorrowedIncrement_native_count n (.gate (.builtin "toffoli"))

/-- Exact all-width count of executed primitive events. -/
theorem hrsControlledBorrowedIncrement_event_count (n : Nat) :
    (controlledBorrowedIncrementProgram n).eventCost.card =
      4 * n + 20 * (n - 1) + 4 * (n - 2) := by
  rw [controlledBorrowedIncrementProgram, programList_eventCost_card]
  have h := increment_weight n (fun _ => 1)
  have hone : ((controlledBorrowedIncrementGates n).map fun _ => (1 : Nat)).sum =
      (controlledBorrowedIncrementGates n).length := by simp
  rw [hone] at h
  omega

/-- Unit-duration serial depth of the actual lowered list. -/
theorem hrsControlledBorrowedIncrement_serial_depth (n : Nat) :
    (controlledBorrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
      4 * n + 20 * (n - 1) + 4 * (n - 2) := by
  calc
    (controlledBorrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
        (controlledBorrowedIncrementProgram n).eventCost.card := by
          rw [controlledBorrowedIncrementProgram, programList_evaluatedEventDepth_unit,
            programList_eventCost_card]
    _ = _ := hrsControlledBorrowedIncrement_event_count n

end

end QuantumAlg.MAU.Addition.HRS
