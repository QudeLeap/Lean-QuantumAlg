/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Prepared
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Coefficient.Window.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Address.Coefficient.Runtime.Resources
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Resources

/-! # Actual complete coefficient-address compute/arithmetic/uncompute resources -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress

noncomputable section

open EncodedBit

/-- Exact Toffolis include both actual coherent phase-address words and the complete body. -/
lemma p256_program_toffoli_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide) signed).eventCost =
        696 + (if signed then 7839 else 6545) := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, ArithmeticAddress.p256_runtimeCoefficientProgram_counts.1,
    CoefficientWindow.p256_program_toffoli_count]

/-- All public-load controlled CNOTs execute in both actual address orientations. -/
lemma p256_program_cnot_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide) signed).eventCost = 3160 := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, ArithmeticAddress.p256_runtimeCoefficientProgram_counts.2.1,
    CoefficientWindow.p256_program_cnot_count]

/-- Every source-phase mask and unary scan X remains in the actual native ledger. -/
lemma p256_program_singleQubit_count (signed : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide) signed).eventCost = 3196 := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, ArithmeticAddress.p256_runtimeCoefficientProgram_counts.2.2,
    CoefficientWindow.p256_program_singleQubit_count]

/-- This duration belongs to the same literal native compute/body/full-adjoint program. -/
lemma p256_program_quantumTime (signed : Bool) :
    (program 256 (by decide) signed).evaluatedEventDepth Resource.Event.quantumDuration =
      704 + (if signed then 14187 else 12893) := by
  rw [program, PredicateCompute.program_quantumTime,
    ArithmeticAddress.p256_runtimeCoefficientProgram_quantumTime,
    CoefficientWindow.p256_program_quantumTime]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.CoefficientAddress
