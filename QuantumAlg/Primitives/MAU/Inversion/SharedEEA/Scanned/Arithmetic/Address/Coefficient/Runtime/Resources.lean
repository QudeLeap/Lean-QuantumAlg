/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Runtime
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Native.Resources
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-! # Actual native resource counts of the coherent source-phase address selection -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- Both actual controlled phase words pay every native metadata CNOT and controlled Toffoli. -/
lemma runtimeCoefficientProgram_toffoli_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (runtimeCoefficientProgram width positive).eventCost =
        3 * (ScanMetadata.addressWidth width + 2 * (ScanMetadata.addressWidth width - 1) +
          2 * (ScanMetadata.addressWidth width - 2) +
          8 * (ScanMetadata.addressWidth width - 1)) := by
  simp only [runtimeCoefficientProgram, GateSpec.programList_toffoli_count_eq_sum,
    runtimeCoefficientGates, GateSpec.choiceGates, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, GateSpec.toffoliMultiplicity,
    GateSpec.listWithDirtyControl_toffoliMultiplicity_sum, nativeCoefficientGates_cnot_count,
    nativeCoefficientGates_toffoli_count, Bool.false_eq_true, if_false, if_true]
  omega

/-- The public source constant becomes actual CNOTs under its retained phase control. -/
lemma runtimeCoefficientProgram_cnot_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (runtimeCoefficientProgram width positive).eventCost =
        (Word.constantOneIndices (coefficientConstant width).toFin).length := by
  simp only [runtimeCoefficientProgram, GateSpec.programList_cnot_count_eq_sum,
    runtimeCoefficientGates, GateSpec.choiceGates, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, GateSpec.cnotMultiplicity,
    GateSpec.listWithDirtyControl_cnotMultiplicity_sum, nativeCoefficientGates_x_count,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add, Nat.add_zero]

/-- Both negative phase-control masks remain actual X instructions in the emitted word. -/
lemma runtimeCoefficientProgram_singleQubit_count (width : Nat) (positive : 1 ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (runtimeCoefficientProgram width positive).eventCost = 2 := by
  simp only [runtimeCoefficientProgram, GateSpec.programList_x_count_eq_sum,
    runtimeCoefficientGates, GateSpec.choiceGates, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons, GateSpec.xMultiplicity,
    GateSpec.listWithDirtyControl_xMultiplicity_sum]

/-- Exact P-256 coordinates come from the same complete actual native source-phase choice. -/
lemma p256_runtimeCoefficientProgram_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (runtimeCoefficientProgram 256 (by decide)).eventCost = 348 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (runtimeCoefficientProgram 256 (by decide)).eventCost = 2 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (runtimeCoefficientProgram 256 (by decide)).eventCost = 2 := by
  rw [runtimeCoefficientProgram_toffoli_count, runtimeCoefficientProgram_cnot_count,
    runtimeCoefficientProgram_singleQubit_count]
  decide

/-- Its actual serial dependency duration retains both controlled words and both masks. -/
lemma p256_runtimeCoefficientProgram_quantumTime :
    (runtimeCoefficientProgram 256 (by decide)).evaluatedEventDepth
      Resource.Event.quantumDuration = 352 := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty)
    (runtimeCoefficientGates 256 (by decide))
  change GateSpec.primitiveEventCount (runtimeCoefficientProgram 256 (by decide)) = _ at native
  rw [GateSpec.primitiveEventCount, p256_runtimeCoefficientProgram_counts.1,
    p256_runtimeCoefficientProgram_counts.2.1,
    p256_runtimeCoefficientProgram_counts.2.2] at native
  rw [runtimeCoefficientProgram, GateSpec.programList_quantumTime, ← native]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAddress
