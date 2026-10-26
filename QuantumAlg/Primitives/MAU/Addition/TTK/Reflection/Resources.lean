/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Reflection.Controlled
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Actual native ledger of the generic fixed-constant reflection -/

namespace QuantumAlg.MAU.Addition.TTK.Reflection

noncomputable section

open EncodedBit GateSpec

lemma gates_xMultiplicity (width : Nat) (constant : Fin (2 ^ width)) :
    ((gates width constant).map xMultiplicity).sum =
      2 * (EncodedBit.Word.constantOneIndices constant).length + width := by
  have low : ((lowRippleGates width).map xMultiplicity).sum = 0 := by
    have actual := ttkLowRipple_native_count width (.gate .singleQubit)
    rw [lowRippleProgram, programList_x_count_eq_sum] at actual
    simpa using actual
  simp only [gates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_xMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates, List.map_reverse, List.sum_reverse, low]
  have complemented : (((rightWord width).complementGates).map xMultiplicity).sum = width := by
    simp [EncodedBit.Word.complementGates, xMultiplicity, Function.comp_def]
  rw [complemented]
  omega

lemma gates_cnotMultiplicity (width : Nat) (constant : Fin (2 ^ width)) :
    ((gates width constant).map cnotMultiplicity).sum =
      width + 2 * (width - 1) + 2 * (width - 2) := by
  have low : ((lowRippleGates width).map cnotMultiplicity).sum =
      width + 2 * (width - 1) + 2 * (width - 2) := by
    simpa only [lowRippleProgram, programList_cnot_count_eq_sum] using
      ttkLowRipple_cnot_count width
  simp only [gates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates, List.map_reverse, List.sum_reverse, low]
  have complemented : (((rightWord width).complementGates).map cnotMultiplicity).sum = 0 := by
    simp [EncodedBit.Word.complementGates, cnotMultiplicity, Function.comp_def]
  rw [complemented]
  omega

lemma gates_toffoliMultiplicity (width : Nat) (constant : Fin (2 ^ width)) :
    ((gates width constant).map toffoliMultiplicity).sum = 2 * (width - 1) := by
  have low : ((lowRippleGates width).map toffoliMultiplicity).sum = 2 * (width - 1) := by
    simpa only [lowRippleProgram, programList_toffoli_count_eq_sum] using
      ttkLowRipple_toffoli_count width
  simp only [gates, List.map_append, List.sum_append,
    EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates, List.map_reverse, List.sum_reverse, low]
  have complemented : (((rightWord width).complementGates).map toffoliMultiplicity).sum = 0 := by
    simp [EncodedBit.Word.complementGates, toffoliMultiplicity, Function.comp_def]
  rw [complemented]
  omega

namespace Controlled

variable {Rest : Type} (rest : BinaryLabelEncoding Rest)
  (width : Nat) (constant : Fin (2 ^ width)) (control work : EncodedBit rest)
  (different : control.wire ≠ work.wire)

lemma program_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program rest width constant control work different).eventCost = 0 := by
  rw [program, programList_x_count_eq_sum, gates, listWithDirtyControl_xMultiplicity_sum]

lemma program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program rest width constant control work different).eventCost =
        2 * (EncodedBit.Word.constantOneIndices constant).length + width := by
  rw [program, programList_cnot_count_eq_sum, gates, listWithDirtyControl_cnotMultiplicity_sum]
  have same := map_event_prodLeft (oracles := .empty) rest (Reflection.gates width constant)
  rw [sum_xMultiplicity_eq_of_events_eq .empty same]
  exact Reflection.gates_xMultiplicity width constant

lemma program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program rest width constant control work different).eventCost =
        width + 10 * (width - 1) + 2 * (width - 2) := by
  rw [program, programList_toffoli_count_eq_sum, gates,
    listWithDirtyControl_toffoliMultiplicity_sum]
  have same := map_event_prodLeft (oracles := .empty) rest (Reflection.gates width constant)
  rw [sum_cnotMultiplicity_eq_of_events_eq .empty same,
    sum_toffoliMultiplicity_eq_of_events_eq .empty same,
    Reflection.gates_cnotMultiplicity, Reflection.gates_toffoliMultiplicity]
  omega

/-- This actual serial control word charges every emitted CNOT and Toffoli once. -/
lemma program_quantumTime :
    (program rest width constant control work different).evaluatedEventDepth
      Resource.Event.quantumDuration =
        2 * (EncodedBit.Word.constantOneIndices constant).length +
          2 * width + 10 * (width - 1) + 2 * (width - 2) := by
  have length := length_eq_multiplicity_sums (gates rest width constant control work different)
  rw [← programList_x_count_eq_sum (layout := QubitLayout.canonical _) (oracles := .empty),
    ← programList_cnot_count_eq_sum (layout := QubitLayout.canonical _) (oracles := .empty),
    ← programList_toffoli_count_eq_sum (layout := QubitLayout.canonical _) (oracles := .empty)]
    at length
  change (gates rest width constant control work different).length =
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program rest width constant control work different).eventCost +
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program rest width constant control work different).eventCost +
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program rest width constant control work different).eventCost at length
  rw [program_x_count, program_cnot_count, program_toffoli_count] at length
  rw [program, programList_quantumTime]
  omega

/-- No constant mask can exceed the original word width, including the zero-width case. -/
lemma program_quantumTime_le :
    (program rest width constant control work different).evaluatedEventDepth
      Resource.Event.quantumDuration ≤
        4 * width + 10 * (width - 1) + 2 * (width - 2) := by
  rw [program_quantumTime]
  have count := EncodedBit.Word.constantOneIndices_length_le constant
  omega

end Controlled

end

end QuantumAlg.MAU.Addition.TTK.Reflection
