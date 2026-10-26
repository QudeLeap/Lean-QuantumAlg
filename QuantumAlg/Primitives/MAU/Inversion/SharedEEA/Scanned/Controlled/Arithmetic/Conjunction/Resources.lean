/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Conjunction
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Phase.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Validity.Resources

/-! # Complete actual four-call control-fused arithmetic conjunction resources -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticConjunction

noncomputable section

/-- Both actual full-carry validity traversals and both native controlled phase words execute. -/
lemma p256_program_toffoli_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 signed coefficient).eventCost =
        1064 + 8 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledFrame.liftProgram_eventCost, GeometryValidity.p256_fullProgram_counts.1,
    ControlledArithmeticPhase.p256_program_toffoli_count]
  omega

/-- Real CNOTs include the complete unmodified validity trees and controlled negative masks. -/
lemma p256_program_cnot_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 signed coefficient).eventCost =
        1050 + 2 * ArithmeticGuard.p256_phaseSingleQubit signed coefficient := by
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledFrame.liftProgram_eventCost, GeometryValidity.p256_fullProgram_counts.2.1,
    ControlledArithmeticPhase.p256_program_cnot_count]
  omega

/-- Both full validity calls retain their two actual root masks and all native fork X gates. -/
lemma p256_program_singleQubit_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 signed coefficient).eventCost = 1068 := by
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    ControlledFrame.liftProgram_eventCost, GeometryValidity.p256_fullProgram_counts.2.2,
    ControlledArithmeticPhase.p256_program_singleQubit_count]

/-- The native four-call order charges both full validity dependency schedules. -/
lemma p256_program_quantumTime (signed coefficient : Bool) :
    (program 256 signed coefficient).evaluatedEventDepth Resource.Event.quantumDuration =
      3182 + 2 * ArithmeticGuard.p256_phaseSingleQubit signed coefficient +
        8 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq,
    ControlledFrame.liftProgram_quantumTime, GeometryValidity.p256_fullProgram_quantumTime,
    ControlledArithmeticPhase.p256_program_quantumTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticConjunction
