/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Remainder.Window
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template.Window.Body.Resources
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Signed.Window.Body.Resources

/-! # Resources of the actual original-word low and signed arithmetic placement -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow

noncomputable section

open EncodedBit

/-- The actual placed toffoli coordinate retains both complete native arithmetic modes. -/
lemma p256_program_toffoli_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 signed).eventCost = (if signed then 7839 else 6545) := by
  cases signed with
  | false => exact ArithmeticWindow.p256_program_toffoli_count
  | true => exact ArithmeticSignedWindow.p256_program_toffoli_count

/-- The actual placed cnot coordinate retains both complete native arithmetic modes. -/
lemma p256_program_cnot_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 signed).eventCost = 3156 := by
  cases signed with
  | false => exact ArithmeticWindow.p256_program_cnot_count
  | true => exact ArithmeticSignedWindow.p256_program_cnot_count

/-- The actual placed singleQubit coordinate retains both complete native arithmetic modes. -/
lemma p256_program_singleQubit_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 signed).eventCost = 3192 := by
  cases signed with
  | false => exact ArithmeticWindow.p256_program_single_count
  | true => exact ArithmeticSignedWindow.p256_program_single_count

/-- Default duration is the complete actual six-traversal native dependency duration. -/
lemma p256_program_quantumTime (signed : Bool) :
    (program 256 signed).evaluatedEventDepth Resource.Event.quantumDuration =
      (if signed then 14187 else 12893) := by
  cases signed with
  | false => exact ArithmeticWindow.p256_program_quantumTime
  | true => exact ArithmeticSignedWindow.p256_program_quantumTime

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.RemainderWindow
