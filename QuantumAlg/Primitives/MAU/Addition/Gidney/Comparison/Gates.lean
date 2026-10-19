/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Gates

/-!
# Literal gates for the two-dirty-bit comparison

Expose the extended offset, restoring low offset and final flag X as actual
native instructions. Packing retains physical positions, and pivot zero emits
the empty list [G17, paper.tex:380-389].
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open EncodedBit GateSpec BinaryLabelEncoding

private def packedPlacement (width : Nat) :
    FullPlacement (HRS.oneDirtyEncoding (1 + width)) (encoding width) :=
  FullPlacement.ofEqualWidth _ _ (packingEquiv width) (packingWidth width)
    (gidneyPackingIndex_encode width)

/-- The extended offset instructions use the flag as the high word bit. -/
def packedOffsetGates (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    List (GateSpec (encoding width)) :=
  (HRS.oneDirtyGates (1 + width) constant).map (packedPlacement width).placeGate

/-- Packing preserves the exact extended-word arithmetic action. -/
lemma gidneyPackedOffsetGates_step (width : Nat) (constant : Fin (2 ^ (1 + width)))
    (state : Registers width) :
    stepList (packedOffsetGates width constant) state = packedOffsetOutput constant state := by
  rw [packedOffsetGates, FullPlacement.placeGates_step]
  simp only [FullPlacement.step, packedPlacement,
    HRS.hrsOneDirtyGates_step]
  rfl

/-- Packed instructions retain the original HRS ledger. -/
lemma gidneyPackedOffsetGates_eventCost (width : Nat) (constant : Fin (2 ^ (1 + width))) :
    ResourcePool.ofList ((packedOffsetGates width constant).map (event .empty)) =
      (HRS.oneDirtyProgram (1 + width) constant).eventCost := by
  simp only [packedOffsetGates, List.map_map, Function.comp_def, FullPlacement.placeGate_event]
  exact HRS.hrsOneDirtyGates_eventCost (1 + width) constant

/-- Restore the target word with the original low-word HRS instructions. -/
def lowOffsetGates (width : Nat) (constant : Fin (2 ^ width)) :
    List (GateSpec (encoding width)) :=
  (HRS.oneDirtyGates width constant).map (GateSpec.prodRight bool)

/-- The leading flag is untouched by low-word restoration. -/
lemma gidneyLowOffsetGates_step (width : Nat) (constant : Fin (2 ^ width))
    (state : Registers width) :
    stepList (lowOffsetGates width constant) state = lowOffsetOutput constant state := by
  exact (stepList_prodRight bool (HRS.oneDirtyGates width constant) state).trans
    (congrArg (fun output => (state.1, output))
      (HRS.hrsOneDirtyGates_step width constant state.2))

/-- The low-word instructions retain the original HRS ledger. -/
lemma gidneyLowOffsetGates_eventCost (width : Nat) (constant : Fin (2 ^ width)) :
    ResourcePool.ofList ((lowOffsetGates width constant).map (event .empty)) =
      (HRS.oneDirtyProgram width constant).eventCost := by
  exact (congrArg ResourcePool.ofList
    (map_event_prodRight bool (HRS.oneDirtyGates width constant))).trans
      (HRS.hrsOneDirtyGates_eventCost width constant)

/-- Literal comparison blocks for the nonzero pivot branch. -/
def positiveComparisonGates (width pivot : Nat) : List (GateSpec (encoding width)) :=
  (packedOffsetGates width (extendedNegatedPivot width pivot) ++
    lowOffsetGates width (pivotWord width pivot)) ++ [.x (flagBit width)]

/-- The literal positive-pivot construction xor-toggles the flag and restores both other fields. -/
lemma gidneyPositiveComparisonGates_step (width pivot : Nat)
    (positive : 0 < pivot) (fitted : pivot ≤ 2 ^ width) (state : Registers width) :
    stepList (positiveComparisonGates width pivot) state = comparisonOutput pivot state := by
  simp only [positiveComparisonGates, stepList_append,
    gidneyPackedOffsetGates_step, gidneyLowOffsetGates_step]
  exact gidneyComparison_positive_steps width pivot positive fitted state

/-- The complete comparison instruction list, including the zero-pivot identity branch. -/
def comparisonGates (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    List (GateSpec (encoding width)) :=
  if pivot.val = 0 then [] else positiveComparisonGates width pivot.val

/-- The explicit comparison list has the exact all-input comparison action. -/
lemma gidneyComparisonGates_step (width : Nat) (pivot : Fin (2 ^ width + 1))
    (state : Registers width) :
    stepList (comparisonGates width pivot) state = comparisonOutput pivot.val state := by
  by_cases zero : pivot.val = 0
  · rw [comparisonGates, if_pos zero, zero]
    exact (gidneyComparison_zero width state).symm
  · rw [comparisonGates, if_neg zero]
    exact gidneyPositiveComparisonGates_step width pivot.val (by omega)
      (by have := pivot.isLt; omega) state

/-- Every native multiplicity matches the already derived comparison resource formula. -/
lemma gidneyComparisonGates_eventCost (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    ResourcePool.ofList ((comparisonGates width pivot).map (event .empty)) =
      (comparisonProgram width pivot).eventCost := by
  rw [comparisonGates, gidneyComparison_eventCost]
  split_ifs
  · rfl
  · simp only [positiveComparisonGates, List.map_append, ResourcePool.ofList_append,
      gidneyPackedOffsetGates_eventCost, gidneyLowOffsetGates_eventCost]
    rfl

/-- The exposed comparison list satisfies the independent HRS-based bound. -/
lemma gidneyComparisonGates_length_bound (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    (comparisonGates width pivot).length ≤ comparisonEventBound width := by
  have same := congrArg Multiset.card (gidneyComparisonGates_eventCost width pivot)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at same
  rw [same]
  exact gidneyComparison_event_count_bound width pivot

end

end QuantumAlg.MAU.Addition.Gidney
