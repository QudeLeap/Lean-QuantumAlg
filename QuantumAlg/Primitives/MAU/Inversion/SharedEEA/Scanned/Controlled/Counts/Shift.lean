/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Shift
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Controlled.Shift.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Increment

/-!
# Complete native coordinates of the actual P-256 externally selected shifts

All three original word sweeps and all three complete HRS clock updates
execute. The source sweeps retain their actual three-Toffoli adjacent
swap construction. Every external predicate and inverse predicate is
charged separately, including all negative-condition masks.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledShiftBlock

noncomputable section

open EncodedBit

private lemma increment_pool (width : Nat) :
    ResourcePool.ofList ((SharedEEA.ControlledShift.incrementGates width).map
      (GateSpec.event .empty)) =
        (Addition.HRS.controlledBorrowedIncrementProgram
          (ExtendedClockRegisters.clockWidth width)).eventCost := by
  have trace :
      (SharedEEA.ControlledShift.incrementGates width).map (GateSpec.event .empty) =
        (Addition.HRS.placedIncrementProgram (ExtendedClockRegisters.extra width)
          (ExtendedClockRegisters.clockWidth width)).eventTrace := by
    rw [SharedEEA.ControlledShift.incrementGates_trace,
      SharedEEA.ControlledShift.incrementProgram, ControlPlacement.place_eventTrace,
      ExtendedClockIncrement.program_eventTrace]
  rw [trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact (Addition.HRS.hrsPlacedIncrement_resources _ _ (fun _ => 1)).1

private lemma p256_increment_counts :
    ((SharedEEA.ControlledShift.incrementGates 256).map GateSpec.toffoliMultiplicity).sum = 258 ∧
      ((SharedEEA.ControlledShift.incrementGates 256).map GateSpec.cnotMultiplicity).sum = 22 ∧
      ((SharedEEA.ControlledShift.incrementGates 256).map GateSpec.xMultiplicity).sum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, increment_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_toffoli_count]
    decide
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, increment_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_cnot_count]
    decide
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, increment_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_x_count]

private lemma p256_word_counts :
    ((Work2PhaseRotation.leftGates 256).map GateSpec.toffoliMultiplicity).sum = 774 ∧
      ((Work2PhaseRotation.leftGates 256).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((Work2PhaseRotation.leftGates 256).map GateSpec.xMultiplicity).sum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Work2PhaseRotation.leftGates,
      Word.controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum]
  · rw [Work2PhaseRotation.leftGates,
      Word.controlledAdjacentShiftLeftGates_cnotMultiplicity_sum]
  · rw [Work2PhaseRotation.leftGates, Word.controlledAdjacentShiftLeftGates_xMultiplicity_sum]

private lemma p256_left_counts :
    ((SharedEEA.ControlledShift.leftGates 256).map GateSpec.toffoliMultiplicity).sum = 1032 ∧
      ((SharedEEA.ControlledShift.leftGates 256).map GateSpec.cnotMultiplicity).sum = 22 ∧
      ((SharedEEA.ControlledShift.leftGates 256).map GateSpec.xMultiplicity).sum = 0 := by
  have placed := SharedEEA.ControlledShift.placed_trace 256 (Work2PhaseRotation.leftGates 256)
  have toffoli := GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty placed
  have cnot := GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty placed
  have single := GateSpec.sum_xMultiplicity_eq_of_events_eq .empty placed
  simp only [SharedEEA.ControlledShift.leftGates, List.map_append, List.sum_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [toffoli, p256_word_counts.1, p256_increment_counts.1]
  · rw [cnot, p256_word_counts.2.1, p256_increment_counts.2.1]
  · rw [single, p256_word_counts.2.2, p256_increment_counts.2.2]

private lemma p256_right_counts :
    ((SharedEEA.ControlledShift.rightGates 256).map GateSpec.toffoliMultiplicity).sum = 1032 ∧
      ((SharedEEA.ControlledShift.rightGates 256).map GateSpec.cnotMultiplicity).sum = 22 ∧
      ((SharedEEA.ControlledShift.rightGates 256).map GateSpec.xMultiplicity).sum = 0 := by
  have placed := SharedEEA.ControlledShift.placed_trace 256 (Work2PhaseRotation.rightGates 256)
  have toffoli := GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty placed
  have cnot := GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty placed
  have single := GateSpec.sum_xMultiplicity_eq_of_events_eq .empty placed
  simp only [SharedEEA.ControlledShift.rightGates, List.map_append, List.sum_append,
    List.map_reverse, List.sum_reverse]
  refine ⟨?_, ?_, ?_⟩
  · rw [toffoli, Work2PhaseRotation.rightGates, List.map_reverse, List.sum_reverse,
      p256_word_counts.1, p256_increment_counts.1]
  · rw [cnot, Work2PhaseRotation.rightGates, List.map_reverse, List.sum_reverse,
      p256_word_counts.2.1, p256_increment_counts.2.1]
  · rw [single, Work2PhaseRotation.rightGates, List.map_reverse, List.sum_reverse,
      p256_word_counts.2.2, p256_increment_counts.2.2]

/-- Both source shift directions and all four actual selected predicates execute in each block. -/
lemma p256_program_toffoli_count (selected : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 selected).eventCost = 3106 := by
  simp only [program, GateSpec.programList_toffoli_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_toffoli_count,
    ControlledSourceWord.selectedGates_toffoli_count, List.map_reverse, List.sum_reverse,
    p256_left_counts.1, p256_right_counts.1]
  cases selected <;> rfl

/-- The actual negative-phase branch retains six additional native predicate-mask CNOTs. -/
lemma p256_program_cnot_count (selected : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 selected).eventCost = if selected then 66 else 72 := by
  simp only [program, GateSpec.programList_cnot_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_cnot_count,
    ControlledSourceWord.selectedGates_cnot_count, List.map_reverse, List.sum_reverse,
    p256_left_counts.2.1, p256_right_counts.2.1]
  cases selected <;> rfl

/-- All source X masks are inside the actual selected predicate lowerings and become CNOTs. -/
lemma p256_program_singleQubit_count (selected : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 selected).eventCost = 0 := by
  simp only [program, GateSpec.programList_x_count_eq_sum, gates,
    List.map_append, List.sum_append, ControlledSourceWord.liftedGates_x_count,
    ControlledSourceWord.selectedGates_x_count,
    p256_left_counts.2.2, p256_right_counts.2.2, Nat.zero_add]

/-- The complete literal shift word has the sequential duration of its actual native gates. -/
lemma p256_program_quantumTime (selected : Bool) :
    (program 256 selected).evaluatedEventDepth Resource.Event.quantumDuration =
      if selected then 3172 else 3178 := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (gates 256 selected)
  change GateSpec.primitiveEventCount (program 256 selected) = _ at native
  rw [GateSpec.primitiveEventCount, p256_program_toffoli_count,
    p256_program_cnot_count, p256_program_singleQubit_count] at native
  rw [program, GateSpec.programList_quantumTime, ← native]
  cases selected <;> decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledShiftBlock
