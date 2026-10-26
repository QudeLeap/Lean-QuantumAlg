/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Resources
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources

/-! # Native counts of the complete literal P-256 modular-addition body -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

private lemma addition_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus additionProgram.eventCost =
      ResourcePool.count focus (MAU.Addition.TTK.overflowProgram width).eventCost +
        ResourcePool.count focus complementCarryProgram.eventCost +
          ResourcePool.count focus sparseComplementProgram.eventCost +
            ResourcePool.count focus (MAU.Addition.TTK.comparisonProgram width).eventCost := by
  simp only [additionProgram, additionGates, MAU.Addition.TTK.overflowProgram,
    complementCarryProgram, sparseComplementProgram, MAU.Addition.TTK.comparisonProgram,
    programList_eventCost, ResourcePool.count_ofList, List.map_append, List.count_append]

/-- The actual sum, comparison and complete sparse correction are all charged. -/
lemma addition_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      additionProgram.eventCost = 5102 := by
  rw [addition_event_count, MAU.Addition.TTK.ttkOverflow_cnot_count,
    complementCarry_cnot_count, sparseComplement_cnot_count,
    MAU.Addition.TTK.ttkComparison_cnot_count]
  rfl

/-- Every carry, borrowed increment and actual flag-cleanup comparison is included. -/
lemma addition_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      additionProgram.eventCost = 15748 := by
  rw [addition_event_count, MAU.Addition.TTK.ttkOverflow_toffoli_count,
    complementCarry_toffoli_count, sparseComplement_toffoli_count,
    MAU.Addition.TTK.ttkComparison_toffoli_count]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
