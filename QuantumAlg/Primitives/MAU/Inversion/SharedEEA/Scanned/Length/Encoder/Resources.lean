/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Height
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Counts

/-! # Exact actual native coordinates of the placed P-256 first-one encoder -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- The placed encoder uses the other original word and no new system: actual closed gate counts. -/
lemma p256_counts (field : Field) (first : Bool) (full : 256 + 3 ≤ 2 ^ 10) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program 256 field first (height 256) (height_capacity 256 full)
          (height_fits 256)).eventCost = 7868 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program 256 field first (height 256) (height_capacity 256 full)
          (height_fits 256)).eventCost = 519 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program 256 field first (height 256) (height_capacity 256 full)
          (height_fits 256)).eventCost = 4196 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).eventCost = 7868 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).eventCost = 519 ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).eventCost = 4196
  exact (bank 256 field first).manyDirtyEncoder259_counts (by decide)

/-- The same placed actual native list has this exact sequential quantum duration. -/
lemma p256_quantumTime (field : Field) (first : Bool) (full : 256 + 3 ≤ 2 ^ 10) :
    (program 256 field first (height 256) (height_capacity 256 full)
      (height_fits 256)).evaluatedEventDepth Resource.Event.quantumDuration = 12583 := by
  change
    ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).evaluatedEventDepth
      Resource.Event.quantumDuration = 12583
  have counted := (bank 256 field first).manyDirtyEncoder259_unitDepth (by decide)
  have duration := UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)) .empty .empty
  change
    ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).evaluatedEventDepth
        Resource.Event.quantumDuration =
      ((bank 256 field first).policy.encoderProgram 9 (by decide) (by decide)).evaluatedEventDepth
        (fun _ => 1) at duration
  exact duration.trans counted

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthEncoder
