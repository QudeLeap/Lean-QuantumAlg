/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.BitCount
import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Arithmetic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Initialization.Length
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Comparison
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Gidney
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Initialization
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Program.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.SourceProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Work1Constant
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters

/-!
# Exact native coordinates of the actual controlled P-256 initialization

Both full source words execute: the comparison/flag/reflection input
fold and every candidate of the actual leading-length writer. Only
their real emitted native lists receive the existing external C/W
lowering. The separate port loader retains its actual fixed mask.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledInitialization

noncomputable section

open EncodedBit ControlledCounts

private abbrev p256 := EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma fold_events (modulus : Nat) :
    (FoldProgram.gates modulus).map (GateSpec.event .empty) =
      (FoldProgram.sourceGates modulus).map (GateSpec.event .empty) :=
  FoldComparisonPlacement.foldComparison_placeGates_trace modulus.size
    (FoldProgram.sourceGates modulus)

private lemma p256_fold_source_counts :
    ((FoldProgram.gates p256).map GateSpec.toffoliMultiplicity).sum = 279556 ∧
      ((FoldProgram.gates p256).map GateSpec.cnotMultiplicity).sum = 17061 ∧
      ((FoldProgram.gates p256).map GateSpec.xMultiplicity).sum = 3223 := by
  have comparison := comparison_source_counts (FoldSourceProgram.wordWidth p256)
    (FoldSourceProgram.comparisonPivot p256)
  have reflection := biFlip_source_counts (FoldSourceProgram.wordWidth p256)
    (by unfold FoldSourceProgram.wordWidth; omega) (FoldSourceProgram.reflectionPivot p256)
  have comparisonNumeric := p256_comparison_numeric
  have reflectionNumeric := p256_reflection_numeric
  rw [comparisonNumeric.1, comparisonNumeric.2.1, comparisonNumeric.2.2] at comparison
  rw [reflectionNumeric.1, reflectionNumeric.2] at reflection
  have placed := fold_events p256
  refine ⟨?_, ?_, ?_⟩
  · rw [GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty placed]
    simp only [FoldProgram.sourceGates, List.map_append, List.sum_append,
      comparison.1, reflection.2.2]
    rfl
  · rw [GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty placed]
    simp only [FoldProgram.sourceGates, List.map_append, List.sum_append,
      comparison.2.1, reflection.2.1]
    rfl
  · rw [GateSpec.sum_xMultiplicity_eq_of_events_eq .empty placed]
    simp only [FoldProgram.sourceGates, List.map_append, List.sum_append,
      comparison.2.2, reflection.1]
    rfl

private lemma p256_source_counts :
    ((gates p256).map GateSpec.toffoliMultiplicity).sum = 1189427 ∧
      ((gates p256).map GateSpec.cnotMultiplicity).sum = 17070 ∧
      ((gates p256).map GateSpec.xMultiplicity).sum = 466321 := by
  have lengthCounts :
      ((InitialLengthWrite.gates p256.size).map GateSpec.toffoliMultiplicity).sum = 909871 ∧
        ((InitialLengthWrite.gates p256.size).map GateSpec.cnotMultiplicity).sum = 9 ∧
        ((InitialLengthWrite.gates p256.size).map GateSpec.xMultiplicity).sum = 463098 :=
    by
      have size : p256.size = 256 := p256_size
      refine ⟨?_, ?_, ?_⟩
      · exact (congrArg (fun width =>
          ((InitialLengthWrite.gates width).map GateSpec.toffoliMultiplicity).sum) size).trans
            p256_initial_length_source_counts.1
      · exact (congrArg (fun width =>
          ((InitialLengthWrite.gates width).map GateSpec.cnotMultiplicity).sum) size).trans
            p256_initial_length_source_counts.2.1
      · exact (congrArg (fun width =>
          ((InitialLengthWrite.gates width).map GateSpec.xMultiplicity).sum) size).trans
            p256_initial_length_source_counts.2.2
  simp only [gates, List.map_append, List.sum_append,
    p256_fold_source_counts.1, p256_fold_source_counts.2.1, p256_fold_source_counts.2.2,
    lengthCounts.1, lengthCounts.2.1, lengthCounts.2.2, true_and]

/-- Every actual fold and initial length native Toffoli/CNOT receives its paid external lowering. -/
lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program p256).eventCost = 4774778 := by
  rw [program, ControlledSourceWord.program_toffoli_count,
    p256_source_counts.1, p256_source_counts.2.1]

/-- All original fold and initial-length X gates become actual CNOTs. -/
lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program p256).eventCost = 466321 := by
  rw [program, ControlledSourceWord.program_cnot_count, p256_source_counts.2.2]

/-- The real externally selected initialization emits no native single-qubit gate. -/
lemma p256_program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program p256).eventCost = 0 :=
  ControlledSourceWord.program_singleQubit_count _ _

/-- The complete literal selected word retains the duration of every actual emitted instruction. -/
lemma p256_program_quantumTime :
    (program p256).evaluatedEventDepth Resource.Event.quantumDuration = 5241099 := by
  rw [program, ControlledSourceWord.program_quantumTime,
    p256_source_counts.1, p256_source_counts.2.1, p256_source_counts.2.2]

private lemma p256_load_source_counts :
    ((Work1Constant.gates p256.size (InitialPortProgram.constant p256)).map
        GateSpec.toffoliMultiplicity).sum = 0 ∧
      ((Work1Constant.gates p256.size (InitialPortProgram.constant p256)).map
        GateSpec.cnotMultiplicity).sum = 0 ∧
      ((Work1Constant.gates p256.size (InitialPortProgram.constant p256)).map
        GateSpec.xMultiplicity).sum = 127 := by
  rw [Work1Constant.gates, Word.xorConstantGates_toffoliMultiplicity_sum,
    Word.xorConstantGates_cnotMultiplicity_sum, Word.xorConstantGates_xMultiplicity_sum]
  exact ⟨rfl, rfl, p256_load_mask_population⟩

/-- Loading uses the exact actual fixed set-bit mask on the original port. -/
lemma p256_loadProgram_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (loadProgram p256).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (loadProgram p256).eventCost = 127 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (loadProgram p256).eventCost = 0 := by
  simp only [loadProgram, ControlledSourceWord.program_toffoli_count,
    ControlledSourceWord.program_cnot_count, ControlledSourceWord.program_singleQubit_count,
    p256_load_source_counts.1, p256_load_source_counts.2.1, p256_load_source_counts.2.2, true_and]

/-- Every actual selected loader CNOT contributes its real serial dependency duration. -/
lemma p256_loadProgram_quantumTime :
    (loadProgram p256).evaluatedEventDepth Resource.Event.quantumDuration = 127 := by
  rw [loadProgram, ControlledSourceWord.program_quantumTime,
    p256_load_source_counts.1, p256_load_source_counts.2.1, p256_load_source_counts.2.2]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledInitialization
