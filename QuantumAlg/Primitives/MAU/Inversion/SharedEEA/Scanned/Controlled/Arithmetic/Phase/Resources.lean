/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Phase.Resources

/-! # Exact native cost of the actual externally selected small source-phase words -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticPhase

noncomputable section

open EncodedBit

private lemma original_toffoli_sum (signed coefficient : Bool) :
    ((ArithmeticGuard.gates 256 signed coefficient).map GateSpec.toffoliMultiplicity).sum =
      ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  have actual := ArithmeticGuard.p256_program_toffoli_count signed coefficient
  rw [ArithmeticGuard.program, GateSpec.programList_toffoli_count_eq_sum] at actual
  exact actual

private lemma original_cnot_sum (signed coefficient : Bool) :
    ((ArithmeticGuard.gates 256 signed coefficient).map GateSpec.cnotMultiplicity).sum = 0 := by
  have actual := ArithmeticGuard.p256_program_cnot_count signed coefficient
  rw [ArithmeticGuard.program, GateSpec.programList_cnot_count_eq_sum] at actual
  exact actual

private lemma original_x_sum (signed coefficient : Bool) :
    ((ArithmeticGuard.gates 256 signed coefficient).map GateSpec.xMultiplicity).sum =
      ArithmeticGuard.p256_phaseSingleQubit signed coefficient := by
  have actual := ArithmeticGuard.p256_program_singleQubit_count signed coefficient
  rw [ArithmeticGuard.program, GateSpec.programList_x_count_eq_sum] at actual
  exact actual

/-- Native dirty-work lowering pays four actual Toffolis for each original source Toffoli. -/
lemma p256_program_toffoli_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 signed coefficient).eventCost =
        4 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (ExternalWord.program (Scanned.encoding 256)
      (ArithmeticGuard.gates 256 signed coefficient)).eventCost = _
  rw [ExternalWord.program_toffoli_count, original_toffoli_sum,
    original_cnot_sum, Nat.zero_add]

/-- Each original physical X mask becomes a real CNOT controlled by the supplied external bit. -/
lemma p256_program_cnot_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 signed coefficient).eventCost =
        ArithmeticGuard.p256_phaseSingleQubit signed coefficient := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
    (ExternalWord.program (Scanned.encoding 256)
      (ArithmeticGuard.gates 256 signed coefficient)).eventCost = _
  rw [ExternalWord.program_cnot_count, original_x_sum]

lemma p256_program_singleQubit_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 signed coefficient).eventCost = 0 := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
    (ExternalWord.program (Scanned.encoding 256)
      (ArithmeticGuard.gates 256 signed coefficient)).eventCost = _
  rw [ExternalWord.program_singleQubit_count]

/-- Actual serial duration includes every dirty-control lowering and every retained mask. -/
lemma p256_program_quantumTime (signed coefficient : Bool) :
    (program 256 signed coefficient).evaluatedEventDepth Resource.Event.quantumDuration =
      ArithmeticGuard.p256_phaseSingleQubit signed coefficient +
        4 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  change (ExternalWord.program (Scanned.encoding 256)
    (ArithmeticGuard.gates 256 signed coefficient)).evaluatedEventDepth
      Resource.Event.quantumDuration = _
  rw [ExternalWord.program_quantumTime, original_toffoli_sum,
    original_cnot_sum, original_x_sum, Nat.add_zero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticPhase
