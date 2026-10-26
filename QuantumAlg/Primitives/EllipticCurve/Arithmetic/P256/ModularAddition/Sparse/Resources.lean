/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix

/-! # Native counts of the literal P-256 sparse-complement correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

private lemma sparseComplement_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus sparseComplementProgram.eventCost =
      ResourcePool.count focus (suffixIncrementProgram width le_rfl).eventCost +
        ResourcePool.count focus (suffixIncrementProgram 32 (by decide)).eventCost +
          ResourcePool.count focus (suffixIncrementProgram 64 (by decide)).eventCost +
            ResourcePool.count focus (suffixIncrementProgram 160 (by decide)).eventCost := by
  simp only [sparseComplementProgram, suffixIncrementProgram, programList_eventCost,
    ResourcePool.count_ofList, sparseComplementGates, List.map_append, List.map_reverse,
    List.count_append, List.count_reverse]

/-- Both forward suffixes and both complete reversed suffixes are charged. -/
lemma sparseComplement_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      sparseComplementProgram.eventCost = 1024 := by
  rw [sparseComplement_event_count, suffixIncrement_cnot_count, suffixIncrement_cnot_count,
    suffixIncrement_cnot_count, suffixIncrement_cnot_count]
  rfl

/-- Every native borrowed-wire control and restoration contributes to this exact count. -/
lemma sparseComplement_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      sparseComplementProgram.eventCost = 13200 := by
  rw [sparseComplement_event_count, suffixIncrement_toffoli_count width le_rfl (by decide),
    suffixIncrement_toffoli_count 32 (by decide) (by decide),
    suffixIncrement_toffoli_count 64 (by decide) (by decide),
    suffixIncrement_toffoli_count 160 (by decide) (by decide)]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
