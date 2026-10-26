/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Selection
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SignQuotient
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Quotient.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Increment

/-!
# Complete actual quotient and Sign resources on the P-256 frame

The source quotient word retains both phase guards, both direction
complements and the actual low-counter HRS word. Its real external
lowering executes after the complete paid Sign scan on the same pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSignQuotient

noncomputable section

open EncodedBit

private lemma low_pool (width : Nat) :
    (LowShiftIncrement.program width).eventCost =
      (Addition.HRS.controlledBorrowedIncrementProgram width.size).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, LowShiftIncrement.program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact (Addition.HRS.hrsPlacedIncrement_resources _ _ (fun _ => 1)).1

private lemma p256_source_counts :
    ((PhaseQuotient.gates 256).map GateSpec.toffoliMultiplicity).sum = 206 ∧
      ((PhaseQuotient.gates 256).map GateSpec.cnotMultiplicity).sum = 40 ∧
      ((PhaseQuotient.gates 256).map GateSpec.xMultiplicity).sum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, PhaseQuotient.phaseQuotient_gates_eventCost,
      ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, PhaseQuotient.program_eventTrace]
    simp only [ResourcePool.ofList_append, ResourcePool.count_add]
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, low_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_toffoli_count]
    simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, Multiset.add_zero,
      ResourcePool.count_add, ResourcePool.count_singleton, Resource.Event.gate.injEq,
      reduceCtorEq, if_false, Nat.add_zero, ResourcePool.count_ofList, Nat.zero_add]
    decide
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, PhaseQuotient.phaseQuotient_gates_eventCost,
      ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, PhaseQuotient.program_eventTrace]
    simp only [ResourcePool.ofList_append, ResourcePool.count_add]
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, low_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_cnot_count]
    simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, Multiset.add_zero,
      ResourcePool.count_add, ResourcePool.count_singleton, if_true, Nat.reduceAdd,
      ResourcePool.count_ofList, List.count_replicate_self, Nat.reduceEqDiff]
    decide
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, PhaseQuotient.phaseQuotient_gates_eventCost,
      ← UnitaryCircuit.ofList_eventTrace_eq_eventCost, PhaseQuotient.program_eventTrace]
    simp only [ResourcePool.ofList_append, ResourcePool.count_add]
    rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, low_pool,
      Addition.HRS.hrsControlledBorrowedIncrement_x_count]
    simp [ResourcePool.count_ofList, List.count_replicate, beq_iff_eq]

private lemma p256_quotient_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (ControlledSourceWord.program 256 (PhaseQuotient.gates 256)).eventCost = 864 := by
  rw [ControlledSourceWord.program_toffoli_count,
    p256_source_counts.1, p256_source_counts.2.1]

private lemma p256_quotient_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (ControlledSourceWord.program 256 (PhaseQuotient.gates 256)).eventCost = 0 := by
  rw [ControlledSourceWord.program_cnot_count, p256_source_counts.2.2]

private lemma p256_quotient_quantumTime :
    (ControlledSourceWord.program 256 (PhaseQuotient.gates 256)).evaluatedEventDepth
      Resource.Event.quantumDuration = 864 := by
  rw [ControlledSourceWord.program_quantumTime,
    p256_source_counts.1, p256_source_counts.2.1, p256_source_counts.2.2]

/-- Both the complete actual Sign scan and selected quotient arithmetic retain their Toffolis. -/
lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 1731 := by
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledSelection.p256_program_counts.1, p256_quotient_toffoli_count]

/-- Actual CNOTs include the entire address preparation and selected Sign scan. -/
lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 984 := by
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledSelection.p256_program_counts.2.1, p256_quotient_cnot_count]

/-- Every actual single-qubit instruction belongs to the complete paid Sign scan. -/
lemma p256_program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 540 := by
  rw [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledSelection.p256_program_counts.2.2,
    ControlledSourceWord.program_singleQubit_count, Nat.add_zero]

/-- Serial execution retains the actual native scan schedule and every quotient instruction. -/
lemma p256_program_quantumTime_le :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration ≤ 3169 := by
  have scan := ControlledSelection.p256_program_quantumTime_le
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, p256_quotient_quantumTime]
  exact (Nat.add_le_add_right scan 864).trans (by decide)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSignQuotient
