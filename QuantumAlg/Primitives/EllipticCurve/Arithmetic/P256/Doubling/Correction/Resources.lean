/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Correction.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Resources

/-! # Native ledger of the actual low-bit CNOT and three complete suffix traversals -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma correction_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus correctionProgram.eventCost =
      ([.gate .cnot].count focus) +
        ResourcePool.count focus (suffixIncrementProgram 32 (by decide)).eventCost +
          ResourcePool.count focus (suffixIncrementProgram 64 (by decide)).eventCost +
            ResourcePool.count focus (suffixIncrementProgram 160 (by decide)).eventCost := by
  simp only [correctionProgram, suffixIncrementProgram, programList_eventCost,
    ResourcePool.count_ofList, correctionGates, List.map_append, List.map_reverse,
    List.count_append, List.count_reverse, List.map_cons, List.map_nil]
  rfl

/-- One original-flag CNOT replaces the full-width increment on the proved even branch. -/
lemma correction_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      correctionProgram.eventCost = 513 := by
  rw [correction_event_count, suffixIncrement_cnot_count, suffixIncrement_cnot_count,
    suffixIncrement_cnot_count]
  rfl

/-- Every native gate in the other three controlled suffixes and their dirty repairs remains. -/
lemma correction_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      correctionProgram.eventCost = 6572 := by
  rw [correction_event_count,
    suffixIncrement_toffoli_count 32 (by decide) (by decide),
    suffixIncrement_toffoli_count 64 (by decide) (by decide),
    suffixIncrement_toffoli_count 160 (by decide) (by decide)]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Correction
