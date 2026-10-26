/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Specification
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord.Resources

/-! # Native resource coordinates of the selected Sign word -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticBlocks

noncomputable section

open EncodedBit

private lemma sign_program_toffoli_count (width : Nat) (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (ControlledSourceWord.program width (signGates width coefficient)).eventCost =
        if coefficient then 1 else 4 := by
  rw [ControlledSourceWord.program_toffoli_count]
  cases coefficient <;> rfl

private lemma sign_program_cnot_count (width : Nat) (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (ControlledSourceWord.program width (signGates width coefficient)).eventCost =
        if coefficient then 0 else 2 := by
  rw [ControlledSourceWord.program_cnot_count]
  cases coefficient <;> rfl

private lemma sign_program_quantumTime (width : Nat) (coefficient : Bool) :
    (ControlledSourceWord.program width (signGates width coefficient)).evaluatedEventDepth
      Resource.Event.quantumDuration = if coefficient then 1 else 6 := by
  rw [ControlledSourceWord.program_quantumTime]
  cases coefficient <;> rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticBlocks
