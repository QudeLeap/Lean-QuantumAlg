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
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Completion.Decoder
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Completion.Ports
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Gidney
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Control
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Completion
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.Correction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Output.PortProgram
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.SourceProgram
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters

/-!
# Exact native coordinates of actual P-256 decoding, correction and unloading

The full binary-weighted clock decoder remains literal, and correction
retains the original complete internally controlled reflection and both
flag masks. Actual full-word reversal and the terminal constant unload
execute separately. All words receive the same real external lowering.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCompletion

noncomputable section

open EncodedBit ControlledCounts

private abbrev p256 := EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

private lemma p256_correction_source_counts :
    ((OutputCorrection.gates p256).map GateSpec.toffoliMultiplicity).sum = 188908 ∧
      ((OutputCorrection.gates p256).map GateSpec.cnotMultiplicity).sum = 3005 ∧
      ((OutputCorrection.gates p256).map GateSpec.xMultiplicity).sum = 2 := by
  have reflection := biFlip_source_counts (FoldSourceProgram.wordWidth p256)
    (by unfold FoldSourceProgram.wordWidth; omega) (FoldSourceProgram.reflectionPivot p256)
  have numeric := p256_reflection_numeric
  rw [numeric.1, numeric.2] at reflection
  have trace := (OutputCorrection.outputCorrection_gates_trace p256).trans
    ((OutputCorrection.program_eventTrace p256).trans
      (OutputCorrection.sourceGates_trace p256).symm)
  refine ⟨?_, ?_, ?_⟩
  · rw [GateSpec.sum_toffoliMultiplicity_eq_of_events_eq .empty trace]
    simp only [OutputCorrection.sourceGates, List.map_append, List.sum_append, reflection.2.2]
    rfl
  · rw [GateSpec.sum_cnotMultiplicity_eq_of_events_eq .empty trace]
    simp only [OutputCorrection.sourceGates, List.map_append, List.sum_append, reflection.2.1]
    rfl
  · rw [GateSpec.sum_xMultiplicity_eq_of_events_eq .empty trace]
    simp only [OutputCorrection.sourceGates, List.map_append, List.sum_append, reflection.1]
    rfl

private lemma p256_source_counts :
    ((gates p256).map GateSpec.toffoliMultiplicity).sum = 1773286 ∧
      ((gates p256).map GateSpec.cnotMultiplicity).sum = 3005 ∧
      ((gates p256).map GateSpec.xMultiplicity).sum = 2 := by
  have decoder := decoder_source_counts p256.size
  have decoderNumeric : ClockDecodeResources.count p256.size = 1584378 := by
    have size : p256.size = 256 := p256_size
    rw [size]
    decide
  rw [decoderNumeric] at decoder
  simp only [gates, List.map_append, List.sum_append,
    decoder.1, decoder.2.1, decoder.2.2, p256_correction_source_counts.1,
    p256_correction_source_counts.2.1, p256_correction_source_counts.2.2, true_and]

/-- Every original binary-weighted sweep and complete correction remains in the selected ledger. -/
lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program p256).eventCost = 7096149 := by
  rw [program, ControlledSourceWord.program_toffoli_count,
    p256_source_counts.1, p256_source_counts.2.1]

/-- The two original correction masks become two actual native CNOTs. -/
lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program p256).eventCost = 2 := by
  rw [program, ControlledSourceWord.program_cnot_count, p256_source_counts.2.2]

/-- The same real externally selected decoder/correction word has no native single-qubit gate. -/
lemma p256_program_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program p256).eventCost = 0 := ControlledSourceWord.program_singleQubit_count _ _

/-- Actual serial native duration charges every original fixed decoder repetition. -/
lemma p256_program_quantumTime :
    (program p256).evaluatedEventDepth Resource.Event.quantumDuration = 7096151 := by
  rw [program, ControlledSourceWord.program_quantumTime,
    p256_source_counts.1, p256_source_counts.2.1, p256_source_counts.2.2]

private lemma p256_unload_source_counts :
    ((OutputPortProgram.gates p256).map GateSpec.toffoliMultiplicity).sum = 0 ∧
      ((OutputPortProgram.gates p256).map GateSpec.cnotMultiplicity).sum = 387 ∧
      ((OutputPortProgram.gates p256).map GateSpec.xMultiplicity).sum = 130 := by
  have orientation := orientation_source_counts p256.size
  have pairs : 3 * ((p256.size + 3) / 2) = 387 := by
    have size : p256.size = 256 := p256_size
    rw [size]
  rw [pairs] at orientation
  have constantNumeric :
      (Word.constantOneIndices (OutputPortProgram.constant p256)).length = 130 :=
    p256_unload_mask_population
  simp only [OutputPortProgram.gates, List.map_append, List.sum_append,
    orientation.1, orientation.2.1, orientation.2.2, OutputPortProgram.unloadGates,
    Work1Constant.gates, Word.xorConstantGates_toffoliMultiplicity_sum,
    Word.xorConstantGates_cnotMultiplicity_sum, Word.xorConstantGates_xMultiplicity_sum,
    constantNumeric, true_and]

/-- The actual full-word reversal retains all 387 selected source CNOTs as native Toffolis. -/
lemma p256_unloadProgram_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (unloadProgram p256).eventCost = 387 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (unloadProgram p256).eventCost = 130 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (unloadProgram p256).eventCost = 0 := by
  simp only [unloadProgram, ControlledSourceWord.program_toffoli_count,
    ControlledSourceWord.program_cnot_count, ControlledSourceWord.program_singleQubit_count,
    p256_unload_source_counts.1, p256_unload_source_counts.2.1,
    p256_unload_source_counts.2.2, true_and]

/-- Physical reversal and constant unloading both retain their actual serial gate duration. -/
lemma p256_unloadProgram_quantumTime :
    (unloadProgram p256).evaluatedEventDepth Resource.Event.quantumDuration = 517 := by
  rw [unloadProgram, ControlledSourceWord.program_quantumTime,
    p256_unload_source_counts.1, p256_unload_source_counts.2.1, p256_unload_source_counts.2.2]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCompletion
