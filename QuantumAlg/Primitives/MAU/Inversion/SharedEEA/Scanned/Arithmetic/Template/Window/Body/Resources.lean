/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Reverse.Resources

/-!
# Actual resources of the complete six-traversal low-word body

The native ledger includes every full static traversal, both real
descending inverses and all six paid moving-flag preparations. These
counts concern this body; length preparation, signed overflow and word
alignment are separate actual instructions.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow

noncomputable section

open ArithmeticTemplate

/-- The actual P-256 low-word body contains all 6545 native Toffoli instructions. -/
lemma p256_program_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256).eventCost = 6545 := by
  simp only [program, stages, stagesProgram, stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_toffoli_count]
  simp [Resource.Event.gate.injEq]

/-- The same native body includes the six original paid control-copy CNOTs. -/
lemma p256_program_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256).eventCost = 3156 := by
  simp only [program, stages, stagesProgram, stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_cnot_count]
  simp

/-- Every actual unary fork X instruction remains in the native single-qubit ledger. -/
lemma p256_program_single_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 3192 := by
  simp only [program, stages, stagesProgram, stageProgram, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.identity_eventCost, ResourcePool.count_add, ResourcePool.count_zero,
    reverseProgram_eventCost, forwardProgram_eventCost, ResourcePool.count_singleton,
    ArithmeticTemplate.p256_program_single_count]
  simp [Resource.Event.gate.injEq]

/-- The true default dependency depth includes each paid preparation and native inverse. -/
lemma p256_program_quantumTime :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration = 12893 := by
  simp only [program, stages, stagesProgram, stageProgram,
    UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.evaluatedEventDepth_identity,
    reverseProgram_quantumTime, forwardProgram_quantumTime,
    ArithmeticTemplate.p256_program_quantumTime]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticWindow
