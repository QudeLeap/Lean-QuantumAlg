/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.HRS
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Gates

/-!
# Numerical native ledger of the unchanged constant comparison

The nonzero-pivot word retains its extended negative offset, restoring
low offset and actual flag X. Zero pivot retains the original empty
word. Every numerical term is connected to that exact event pool.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit Addition.Gidney

/-- Exact numerical comparison ledger before any additional external control lowering. -/
def comparisonCount (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  if pivot.val = 0 then 0 else
    oneDirtyCount (1 + width) (extendedNegatedPivot width pivot.val) focus +
      oneDirtyCount width (pivotWord width pivot.val) focus +
        (if .gate .singleQubit = focus then 1 else 0)

/-- The numerical formula counts the actual complete comparison's event pool coordinate. -/
lemma comparisonCount_eq (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (comparisonProgram width pivot).eventCost =
      comparisonCount width pivot focus := by
  by_cases zero : pivot.val = 0
  · rw [gidneyComparison_eventCost, if_pos zero, comparisonCount, if_pos zero]
    exact ResourcePool.count_zero _
  · rw [gidneyComparison_eventCost, if_neg zero, comparisonCount, if_neg zero,
      ResourcePool.count_add, ResourcePool.count_add, oneDirtyCount_eq,
      oneDirtyCount_eq, ResourcePool.count_singleton]

private lemma comparison_pool (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    ResourcePool.ofList ((comparisonGates width pivot).map (GateSpec.event .empty)) =
      (comparisonProgram width pivot).eventCost := gidneyComparisonGates_eventCost width pivot

/-- Each actual emitted comparison coordinate equals its independent numerical formula. -/
lemma comparison_source_counts (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    ((comparisonGates width pivot).map GateSpec.toffoliMultiplicity).sum =
        comparisonCount width pivot (.gate .toffoli) ∧
      ((comparisonGates width pivot).map GateSpec.cnotMultiplicity).sum =
        comparisonCount width pivot (.gate .cnot) ∧
      ((comparisonGates width pivot).map GateSpec.xMultiplicity).sum =
        comparisonCount width pivot (.gate .singleQubit) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← GateSpec.programList_toffoli_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, comparison_pool, comparisonCount_eq]
  · rw [← GateSpec.programList_cnot_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, comparison_pool, comparisonCount_eq]
  · rw [← GateSpec.programList_x_count_eq_sum
      (layout := QubitLayout.canonical _) (oracles := .empty),
      GateSpec.programList_eventCost, comparison_pool, comparisonCount_eq]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
