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

private lemma gate_weight (n : Nat) (gate : EncodedBit.GateSpec (TTK.encoding n))
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((controlledBorrowedGate n gate).map fun emitted => weight (event .empty emitted)).sum =
      gate.xMultiplicity * weight (.gate .cnot) +
        gate.cnotMultiplicity * weight (.gate .toffoli) +
        gate.toffoliMultiplicity * (4 * weight (.gate .toffoli)) := by
  cases gate with
  | x target =>
      simp [controlledBorrowedGate, xMultiplicity, cnotMultiplicity,
        toffoliMultiplicity, EncodedBit.GateSpec.event,
        EncodedBit.GateSpec.primitive, QubitPrimitive.event, QubitPrimitive.nativeToken,
        AlgorithmGate.model, AlgorithmGate.coordinate]
  | cnot source target hst =>
      simp [controlledBorrowedGate, xMultiplicity, cnotMultiplicity,
        toffoliMultiplicity, EncodedBit.GateSpec.event,
        EncodedBit.GateSpec.primitive, QubitPrimitive.event, QubitPrimitive.nativeToken,
        AlgorithmGate.model, AlgorithmGate.coordinate]
  | toffoli a b target hab hat hbt =>
      dsimp only [controlledBorrowedGate, controlledOperandToffoli]
      rw [hrsDirtyControlledToffoli_weight]
      simp [xMultiplicity, cnotMultiplicity, toffoliMultiplicity]

private lemma list_weight (n : Nat) (gates : List (EncodedBit.GateSpec (TTK.encoding n)))
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((controlledBorrowedList n gates).map fun gate => weight (event .empty gate)).sum =
      (gates.map xMultiplicity).sum * weight (.gate .cnot) +
        (gates.map cnotMultiplicity).sum * weight (.gate .toffoli) +
        (gates.map toffoliMultiplicity).sum * (4 * weight (.gate .toffoli)) := by
  induction gates with
  | nil => simp [controlledBorrowedList]
  | cons gate rest ih =>
      change (((controlledBorrowedGate n gate) ++ controlledBorrowedList n rest).map
        fun emitted => weight (event .empty emitted)).sum = _
      rw [List.map_append, List.sum_append, gate_weight, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

private lemma increment_weight (n : Nat)
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    ((controlledBorrowedIncrementGates n).map fun gate => weight (event .empty gate)).sum =
      (2 * n) * weight (.gate .cnot) +
        (2 * n + 20 * (n - 1) + 4 * (n - 2)) * weight (.gate .toffoli) := by
  have h := list_weight n (borrowedIncrementGates n) weight
  rw [← programList_x_count_eq_sum, ← programList_cnot_count_eq_sum,
    ← programList_toffoli_count_eq_sum] at h
  change ((controlledBorrowedIncrementGates n).map
      fun gate => weight (event .empty gate)).sum =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
          (borrowedIncrementProgram n).eventCost * weight (.gate .cnot) +
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
          (borrowedIncrementProgram n).eventCost * weight (.gate .toffoli) +
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (borrowedIncrementProgram n).eventCost * (4 * weight (.gate .toffoli)) at h
  rw [hrsBorrowedIncrement_x_count, hrsBorrowedIncrement_cnot_count,
    hrsBorrowedIncrement_toffoli_count] at h
  rw [h]
  ring

/-- Every native event coordinate comes from the actual controlled expansion. -/
lemma hrsControlledBorrowedIncrement_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (controlledBorrowedIncrementProgram n).eventCost =
      (2 * n) *
        (if (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
          then 1 else 0) +
      (2 * n + 20 * (n - 1) + 4 * (n - 2)) *
        (if (.gate .toffoli : Resource.Event (.quantum AlgorithmGate.model .empty)) = focus
          then 1 else 0) := by
  rw [controlledBorrowedIncrementProgram, programList_event_count_eq_sum_eventMultiplicity]
  exact increment_weight n (fun emitted => if emitted = focus then 1 else 0)

/-- No uncontrolled X leaf remains in the controlled program. -/
lemma hrsControlledBorrowedIncrement_x_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (controlledBorrowedIncrementProgram n).eventCost =
      0 := by
  simpa using hrsControlledBorrowedIncrement_native_count n (.gate .singleQubit)

/-- Each borrowed-word complement contributes one CNOT per bit. -/
lemma hrsControlledBorrowedIncrement_cnot_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (controlledBorrowedIncrementProgram n).eventCost = 2 * n := by
  simpa using hrsControlledBorrowedIncrement_native_count n (.gate .cnot)

/-- Every original CNOT contributes one Toffoli and every original Toffoli four. -/
lemma hrsControlledBorrowedIncrement_toffoli_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (controlledBorrowedIncrementProgram n).eventCost =
      2 * n + 20 * (n - 1) + 4 * (n - 2) := by
  simpa using hrsControlledBorrowedIncrement_native_count n (.gate .toffoli)

/-- Exact all-width count of executed primitive events. -/
lemma hrsControlledBorrowedIncrement_event_count (n : Nat) :
    (controlledBorrowedIncrementProgram n).eventCost.card =
      4 * n + 20 * (n - 1) + 4 * (n - 2) := by
  rw [controlledBorrowedIncrementProgram, programList_eventCost_card]
  have h := increment_weight n (fun _ => 1)
  have hone : ((controlledBorrowedIncrementGates n).map fun _ => (1 : Nat)).sum =
      (controlledBorrowedIncrementGates n).length := by simp
  rw [hone] at h
  omega

/-- Unit-duration serial depth of the actual lowered list. -/
lemma hrsControlledBorrowedIncrement_serial_depth (n : Nat) :
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
