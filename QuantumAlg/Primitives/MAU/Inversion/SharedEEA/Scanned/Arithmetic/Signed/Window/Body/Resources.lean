/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Reverse.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Reverse.Resources

/-!
# Actual resources of the complete six-traversal signed body

The native ledger includes every full static traversal, both real
descending inverses and all six paid moving-flag preparations. These
counts include both fused signed overflow operations. Length preparation,
metadata guards, word alignment and terminal length refresh remain additional
actual instructions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow

noncomputable section

open ArithmeticTemplate

/-- The actual P-256 signed body contains all 7839 native Toffoli instructions. -/
lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 7839 := by
  simp only [program, ArithmeticWindow.stages, stagesProgram, stageProgram,
    ArithmeticWindow.stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ArithmeticSigned.reverseProgram_eventCost,
    ArithmeticSigned.forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_toffoli_count, ArithmeticSigned.p256_program_toffoli_count]
  simp [Resource.Event.gate.injEq]

/-- The same native body includes the six original paid control-copy CNOTs. -/
lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 3156 := by
  simp only [program, ArithmeticWindow.stages, stagesProgram, stageProgram,
    ArithmeticWindow.stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ArithmeticSigned.reverseProgram_eventCost,
    ArithmeticSigned.forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_cnot_count, ArithmeticSigned.p256_program_cnot_count]
  simp

/-- Every actual unary fork X instruction remains in the native single-qubit ledger. -/
lemma p256_program_single_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 3192 := by
  simp only [program, ArithmeticWindow.stages, stagesProgram, stageProgram,
    ArithmeticWindow.stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ArithmeticSigned.reverseProgram_eventCost,
    ArithmeticSigned.forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_single_count, ArithmeticSigned.p256_program_single_count]
  simp [Resource.Event.gate.injEq]

/-- The true default dependency depth includes each paid preparation and native inverse. -/
lemma p256_program_quantumTime :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration = 14187 := by
  simp only [program, ArithmeticWindow.stages, stagesProgram, stageProgram,
    ArithmeticWindow.stageProgram,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_identity,
    reverseProgram_quantumTime, forwardProgram_quantumTime,
    ArithmeticSigned.reverseProgram_quantumTime,
    ArithmeticSigned.forwardProgram_quantumTime,
    ArithmeticTemplate.p256_program_quantumTime, ArithmeticSigned.p256_program_quantumTime]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticSignedWindow
