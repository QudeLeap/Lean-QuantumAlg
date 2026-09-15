/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Native.Alphabet
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.NativeResources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Small.Offset

/-!
# Independent native-coordinate budgets for actual modular offsets

The comparison uses the base primitive coordinates; the coherent bi-flip
uses their once-controlled coordinates. The actual three-pivot program
therefore has the explicit finite support `offsetAlphabet`. Its independent
numerical event envelope bounds each coordinate of that alphabet. Small
offset branches retain the original literal X/CNOT coordinates.
-/

namespace QuantumAlg.MAU.Addition.Gidney

noncomputable section

open Nat.FixedWidth EncodedBit.GateSpec

theorem gidneyComparison_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event .quantum)
    (present : focus ∈ (comparisonProgram width pivot).eventCost) :
    focus ∈ primitiveAlphabet := by
  rw [gidneyComparison_eventCost] at present
  by_cases zero : pivot.val = 0
  · rw [if_pos zero] at present
    simp at present
  · rw [if_neg zero] at present
    rcases Multiset.mem_add.mp present with before | finalX
    · rcases Multiset.mem_add.mp before with extended | low
      · exact HRS.hrsOneDirty_native_support (1 + width) (extendedNegatedPivot width pivot.val)
          focus extended
      · exact HRS.hrsOneDirty_native_support width (pivotWord width pivot.val) focus low
    · have equality : focus = .gate (.builtin "x") := by
        simpa [ResourcePool.singleton] using finalX
      rw [equality]
      simp [primitiveAlphabet, ResourcePool.ofList]

theorem gidneyBiFlip_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event .quantum) (present : focus ∈ (biFlipProgram width pivot).eventCost) :
    focus ∈ ResourcePool.controlForDimension 2 primitiveAlphabet := by
  rw [gidneyBiFlip_eventCost] at present
  change focus ∈ Multiset.map (fun event => event.controlForDimension 2)
    ((HRS.oneDirtyProgram width (negatedPivot width pivot.val)).eventCost +
      (complementProgram width).eventCost) at present
  obtain ⟨event, membership, rfl⟩ := Multiset.mem_map.mp present
  change event.controlForDimension 2 ∈ Multiset.map
    (fun current => current.controlForDimension 2) primitiveAlphabet
  apply Multiset.mem_map.mpr
  refine ⟨event, ?_, rfl⟩
  rcases Multiset.mem_add.mp membership with offset | complement
  · exact HRS.hrsOneDirty_native_support width (negatedPivot width pivot.val) event offset
  · exact programList_native_support (complementGates width) event complement

theorem gidneyPivot_native_support (width : Nat) (pivot : Fin (2 ^ width + 1))
    (focus : Resource.Event .quantum) (present : focus ∈ (pivotProgram width pivot).eventCost) :
    focus ∈ offsetAlphabet := by
  rw [gidneyPivot_eventCost] at present
  simp only [Multiset.mem_add] at present
  rcases present with ((first | second) | third) | fourth
  · exact Multiset.mem_add.mpr (Or.inr (gidneyBiFlip_native_support width pivot focus first))
  · exact Multiset.mem_add.mpr (Or.inl (gidneyComparison_native_support width pivot focus second))
  · exact Multiset.mem_add.mpr (Or.inr (gidneyBiFlip_native_support width pivot focus third))
  · exact Multiset.mem_add.mpr (Or.inl (gidneyComparison_native_support width pivot focus fourth))

/-- Only the six explicit base/once-controlled coordinates occur in the three-pivot offset. -/
theorem gidneyModularOffset_native_support (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) (focus : Resource.Event .quantum)
    (present : focus ∈ (modularOffsetProgram width modulus constant).eventCost) :
    focus ∈ offsetAlphabet := by
  rw [gidneyModularOffset_eventCost] at present
  simp only [Multiset.mem_add] at present
  rcases present with (first | second) | third
  · exact gidneyPivot_native_support width (offsetFirstPivot modulus constant) focus first
  · exact gidneyPivot_native_support width modulus focus second
  · exact gidneyPivot_native_support width (offsetLastPivot modulus constant) focus third

/-- The independent resource pool states a closed cap at each explicit native coordinate. -/
def modularOffsetNativeBudget (width : Nat) : ResourcePool .quantum :=
  modularOffsetEventBound width • offsetAlphabet

theorem gidneyModularOffset_native_bound (width : Nat) (modulus : Fin (2 ^ width + 1))
    (constant : Fin (modulus.val + 1)) :
    (modularOffsetProgram width modulus constant).eventCost ≤ modularOffsetNativeBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (gidneyModularOffset_native_support width modulus constant)
    (gidneyModularOffset_event_count_bound width modulus constant)

theorem gidneySmallPivot_native_support (width : Nat) (small : width ≤ 2)
    (pivot : Fin (2 ^ width + 1)) (focus : Resource.Event .quantum)
    (present : focus ∈ (Small.pivotProgram width small pivot).eventCost) :
    focus ∈ primitiveAlphabet := by
  interval_cases width
  · change focus ∈ (Small.Zero.circuit pivot).eventCost at present
    rw [(Small.Zero.gidneySmallZero_interface pivot).2.1] at present
    simp at present
  · change focus ∈ (Small.One.circuit pivot).eventCost at present
    rw [Small.One.gidneySmallOne_eventCost] at present
    (fin_cases pivot <;> simp [ResourcePool.ofList, primitiveAlphabet] at *); tauto
  · change focus ∈ (Small.Two.circuit pivot).eventCost at present
    rw [Small.Two.gidneySmallTwo_eventCost] at present
    fin_cases pivot <;> simp [ResourcePool.ofList, primitiveAlphabet] at * <;> tauto

/-- Small offsets use only the original primitive labels and allocate no borrowed bits. -/
theorem gidneySmallModularOffset_native_support (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1))
    (focus : Resource.Event .quantum)
    (present : focus ∈ (Small.modularOffsetProgram width small modulus constant).eventCost) :
    focus ∈ primitiveAlphabet := by
  rw [Small.gidneySmallModularOffset_eventCost] at present
  simp only [Multiset.mem_add] at present
  rcases present with (first | second) | third
  · exact gidneySmallPivot_native_support width small
      (offsetFirstPivot modulus constant) focus first
  · exact gidneySmallPivot_native_support width small modulus focus second
  · exact gidneySmallPivot_native_support width small (offsetLastPivot modulus constant) focus third

end

end QuantumAlg.MAU.Addition.Gidney
