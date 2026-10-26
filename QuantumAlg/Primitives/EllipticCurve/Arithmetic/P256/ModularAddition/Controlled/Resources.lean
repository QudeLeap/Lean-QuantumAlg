/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Resources

/-! # Remaining native coordinates of the actual externally controlled modular addition -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

private lemma addition_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      additionProgram.eventCost = 508 := by
  have overflow : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (MAU.Addition.TTK.overflowProgram width).eventCost = 0 := by
    simpa using MAU.Addition.TTK.ttkOverflow_native_count width (.gate .singleQubit)
  have low : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (MAU.Addition.TTK.lowRippleProgram width).eventCost = 0 := by
    simpa using MAU.Addition.TTK.ttkLowRipple_native_count width (.gate .singleQubit)
  have sparse : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      sparseComplementProgram.eventCost = 0 := by
    rw [sparseComplement_event_count]
    simp only [suffixIncrement_eventCost, MAU.Addition.HRS.hrsControlledBorrowedIncrement_x_count]
  rw [addition_event_count, MAU.Addition.TTK.ttkComparison_native_count, overflow,
    complementCarry_x_count, sparse, low]

namespace Controlled

/-- Each of the body's 508 X occurrences becomes one actual externally controlled CNOT. -/
lemma controlledAddition_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      controlledAdditionProgram.eventCost = 508 := by
  rw [controlledAdditionProgram, programList_cnot_count_eq_sum, controlledAdditionGates,
    controlledListWithWorkGates_cnotMultiplicity_sum]
  rw [← programList_x_count_eq_sum
    (layout := QubitLayout.canonical selectorEncoding.width) (oracles := .empty),
    lifted_eventCost, addition_x_count]

/-- Gate-by-gate quantum control leaves no uncontrolled X instruction. -/
lemma controlledAddition_x_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      controlledAdditionProgram.eventCost = 0 := by
  rw [controlledAdditionProgram, programList_x_count_eq_sum, controlledAdditionGates,
    controlledListWithWorkGates_xMultiplicity_sum]

end Controlled

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
