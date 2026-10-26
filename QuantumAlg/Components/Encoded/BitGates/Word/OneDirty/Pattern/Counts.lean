/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Resources

/-! # Exact coordinate counts of actual masked multi-control words -/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}

/-- Masked native conjunctions retain all actual Toffoli and negative-source X occurrences. -/
lemma patternGates_native_counts (layout : OneDirtyLayout (encoding := encoding) controls)
    (enough : 2 ≤ controls) (expected : Fin controls → Bool) :
    ((layout.patternGates expected).map GateSpec.toffoliMultiplicity).sum = gateCount controls ∧
      ((layout.patternGates expected).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((layout.patternGates expected).map GateSpec.xMultiplicity).sum =
        2 * (patternMaskIndices expected).length := by
  have nonzero : controls ≠ 0 := by omega
  have notOne : controls ≠ 1 := by omega
  have trace := layout.patternGates_events .empty expected
  rw [if_neg nonzero, if_neg notOne] at trace
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, trace, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, trace, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq]
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, trace, ResourcePool.count_ofList]
    simp [List.count_replicate, beq_iff_eq, two_mul]

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
