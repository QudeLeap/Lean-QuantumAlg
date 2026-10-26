/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Toggle
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source
import all
  QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Arithmetic.Conjunction.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Geometry.Coefficient.Runtime.Resources
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Resources

/-! # Native coordinates of the actual selected arithmetic guard -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticToggle

noncomputable section

open EncodedBit

private lemma p256_geometry_toffoli_count (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (geometryProgram 256 (by decide) coefficient).eventCost =
        if coefficient then 387 else 60 := by
  cases coefficient
  · exact ArithmeticGeometry.p256_remainderProgram_counts.1
  · exact ArithmeticGeometry.runtimeCoefficientProgram_p256_toffoli

/-- Both complete geometry words and all four native conjunction calls are charged. -/
lemma p256_program_toffoli_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 (by decide) signed coefficient).eventCost =
        2 * (if coefficient then 387 else 60) + 1064 +
          8 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
    (PredicateCompute.program
      (ControlledFrame.liftProgram 256 (geometryProgram 256 (by decide) coefficient))
      (ControlledArithmeticConjunction.program 256 signed coefficient)).eventCost = _
  rw [PredicateCompute.program_eventCost, ResourcePool.count_add, ResourcePool.count_nsmul,
    ControlledFrame.liftProgram_eventCost, p256_geometry_toffoli_count,
    ControlledArithmeticConjunction.p256_program_toffoli_count]
  omega

private lemma p256_geometry_cnot_count (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (geometryProgram 256 (by decide) coefficient).eventCost =
        if coefficient then 4 else 147 := by
  cases coefficient
  · exact ArithmeticGeometry.p256_remainderProgram_counts.2
  · exact ArithmeticGeometry.p256_runtimeCoefficientProgram_cnot_count

private lemma p256_geometry_singleQubit_count (coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (geometryProgram 256 (by decide) coefficient).eventCost = 2 := by
  cases coefficient
  · exact ArithmeticGeometry.p256_remainderProgram_singleQubit_count
  · exact ArithmeticGeometry.p256_runtimeCoefficientProgram_singleQubit_count

private lemma p256_geometry_quantumTime_le (coefficient : Bool) :
    (geometryProgram 256 (by decide) coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration ≤ if coefficient then 393 else 152 := by
  cases coefficient
  · exact ArithmeticGeometry.p256_remainderProgram_quantumTime_le
  · exact ArithmeticGeometry.p256_runtimeCoefficientProgram_quantumTime.le

/-- Both complete geometry orientations and all actual mask-controlled CNOTs are charged. -/
lemma p256_program_cnot_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 (by decide) signed coefficient).eventCost =
        2 * (if coefficient then 4 else 147) + 1050 +
          2 * ArithmeticGuard.p256_phaseSingleQubit signed coefficient := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, ControlledFrame.liftProgram_eventCost,
    p256_geometry_cnot_count, ControlledArithmeticConjunction.p256_program_cnot_count]
  omega

/-- Native validity-fork X gates and both geometry masks remain in the same actual toggle. -/
lemma p256_program_singleQubit_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 (by decide) signed coefficient).eventCost = 1072 := by
  rw [program, PredicateCompute.program_eventCost, ResourcePool.count_add,
    ResourcePool.count_nsmul, ControlledFrame.liftProgram_eventCost,
    p256_geometry_singleQubit_count,
    ControlledArithmeticConjunction.p256_program_singleQubit_count]

/-- The whole native compute/conjunction/adjoint schedule retains the parallel geometry bound. -/
lemma p256_program_quantumTime_le (signed coefficient : Bool) :
    (program 256 (by decide) signed coefficient).evaluatedEventDepth
      Resource.Event.quantumDuration ≤
        2 * (if coefficient then 393 else 152) + 3182 +
          2 * ArithmeticGuard.p256_phaseSingleQubit signed coefficient +
            8 * ArithmeticGuard.p256_phaseToffoli signed coefficient := by
  have geometry := p256_geometry_quantumTime_le coefficient
  rw [program, PredicateCompute.program_quantumTime, ControlledFrame.liftProgram_quantumTime,
    ControlledArithmeticConjunction.p256_program_quantumTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledArithmeticToggle
