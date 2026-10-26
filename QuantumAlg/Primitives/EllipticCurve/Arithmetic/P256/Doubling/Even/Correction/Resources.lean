/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Even.Correction.Program

/-! # Native counts of the actual three-stage even correction -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

private lemma evenSuffix_same_eventCost (length : Nat) (fits : length < width) :
    (evenSuffixProgram length fits).eventCost =
      (suffixIncrementProgram length fits.le).eventCost :=
  (evenSuffix_eventCost length fits).trans (suffixIncrement_eventCost length fits.le).symm

private lemma evenCorrection_event_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus evenCorrectionProgram.eventCost =
      ResourcePool.count focus (suffixIncrementProgram 32 (by decide)).eventCost +
        ResourcePool.count focus (suffixIncrementProgram 64 (by decide)).eventCost +
          ResourcePool.count focus (suffixIncrementProgram 160 (by decide)).eventCost := by
  have lists : ResourcePool.count focus evenCorrectionProgram.eventCost =
      ResourcePool.count focus (evenSuffixProgram 32 (by decide)).eventCost +
        ResourcePool.count focus (evenSuffixProgram 64 (by decide)).eventCost +
          ResourcePool.count focus (evenSuffixProgram 160 (by decide)).eventCost := by
    simp only [evenCorrectionProgram, evenSuffixProgram, programList_eventCost,
      ResourcePool.count_ofList, evenCorrectionGates, List.map_append, List.map_reverse,
      List.count_append, List.count_reverse]
  simpa only [evenSuffix_same_eventCost] using lists

/-- Both native decrements retain and pay their complete reversed instruction lists. -/
lemma evenCorrection_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      evenCorrectionProgram.eventCost = 512 := by
  rw [evenCorrection_event_count, suffixIncrement_cnot_count, suffixIncrement_cnot_count,
    suffixIncrement_cnot_count]

/-- All original low-bit controls and borrowed-source repairs are included. -/
lemma evenCorrection_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      evenCorrectionProgram.eventCost = 6572 := by
  rw [evenCorrection_event_count,
    suffixIncrement_toffoli_count 32 (by decide) (by decide),
    suffixIncrement_toffoli_count 64 (by decide) (by decide),
    suffixIncrement_toffoli_count 160 (by decide) (by decide)]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
