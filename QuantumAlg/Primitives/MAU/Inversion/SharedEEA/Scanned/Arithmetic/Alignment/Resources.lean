/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Pair
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Components

/-! # Paid native two-word alignment resources on the unchanged original EEA carrier -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment

noncomputable section

open EncodedBit

/-- Both actual barrel words contribute every real Fredkin and its common-control duration. -/
lemma pairProgram_resources (width : Nat) (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (pairProgram width field).eventCost ≤ 2 * (width + 3) * width.size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (pairProgram width field).eventCost ≤ 4 * (width + 3) * width.size ∧
      (pairProgram width field).evaluatedEventDepth Resource.Event.quantumDuration
        ≤ 6 * (width + 3) * width.size := by
  have first := (barrel width true field).gates_counts (permutation width)
    (PermutationBarrel.binaryStages width.size)
  have second := (barrel width false field).gates_counts (permutation width)
    (PermutationBarrel.binaryStages width.size)
  simp only [PermutationBarrel.binaryStages, List.length_map, List.length_finRange] at first second
  simp only [pairProgram, GateSpec.programList_toffoli_count_eq_sum,
    GateSpec.programList_cnot_count_eq_sum, GateSpec.programList_quantumTime, pairGates,
    List.map_append, List.sum_append, List.length_append, gates, PermutationBarrel.binaryStages]
  constructor
  · convert Nat.add_le_add first.1 second.1 using 1
    ring
  constructor
  · convert Nat.add_le_add first.2.1 second.2.1 using 1
    ring
  · convert Nat.add_le_add first.2.2 second.2.2 using 1
    ring

/-- P-256 alignment counts only this actual one-way two-word fragment. -/
lemma p256_pairProgram_resources (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (pairProgram 256 field).eventCost ≤ 4662 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (pairProgram 256 field).eventCost ≤ 9324 ∧
      (pairProgram 256 field).evaluatedEventDepth Resource.Event.quantumDuration ≤ 13986 := by
  have actual := pairProgram_resources 256 field
  have size : (256 : Nat).size = 9 := by decide
  norm_num only [size] at actual
  exact actual

/-- Both actual full-word alignment barrels contain only Fredkin's CNOT and Toffoli leaves. -/
lemma pairProgram_singleQubit_count (width : Nat) (field : ArithmeticGeometry.Field) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (pairProgram width field).eventCost = 0 := by
  rw [pairProgram, GateSpec.programList_x_count_eq_sum, pairGates,
    List.map_append, List.sum_append]
  simp only [gates, ControlledCounts.barrel_gates_x_count, Nat.zero_add]


end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment
