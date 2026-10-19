/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled
import all QuantumAlg.Primitives.MAU.Addition.Gidney.BiFlip
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Counts

/-!
# Separate native allowances through the actual two-control construction

The HRS coordinate recurrences pass through the literal bi-flip and comparison
lists, their existing control expansion and the three-pivot accumulator.
Placement and the original BCBC execution remain unchanged
[G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

noncomputable section
open EncodedBit GateSpec
open QuantumAlg.MAU.Addition.HRS
private lemma list_x {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) :
    xCount gates = ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (ResourcePool.ofList (gates.map (event .empty))) := by
  rw [← programList_eventCost (QubitLayout.canonical _) .empty gates,
    programList_x_count_eq_sum]
  rfl
private lemma list_c {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) :
    cCount gates = ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (ResourcePool.ofList (gates.map (event .empty))) := by
  rw [← programList_eventCost (QubitLayout.canonical _) .empty gates,
    programList_cnot_count_eq_sum]
  rfl
private lemma list_t {Data : Type} {carrier : BinaryLabelEncoding Data}
    (gates : List (GateSpec carrier)) :
    tCount gates = ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (ResourcePool.ofList (gates.map (event .empty))) := by
  rw [← programList_eventCost (QubitLayout.canonical _) .empty gates,
    programList_toffoli_count_eq_sum]
  rfl
private lemma biFlipBody_bounds (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    xCount (Addition.Gidney.biFlipBodyGates width pivot) ≤ oneDirtyXBound width + width ∧
    cCount (Addition.Gidney.biFlipBodyGates width pivot) ≤ oneDirtyCnotBound width ∧
    tCount (Addition.Gidney.biFlipBodyGates width pivot) ≤ oneDirtyToffoliBound width := by
  have complement : ResourcePool.ofList
      ((Addition.Gidney.complementBodyGates width).map (event .empty)) =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) width := by
    change ResourcePool.ofList (((Addition.Gidney.complementGates width).map
      (GateSpec.prodLeft BinaryLabelEncoding.bool)).map (event .empty)) = _
    rw [map_event_prodLeft]
    simpa only [Addition.Gidney.complementProgram, programList_eventCost,
      ResourcePool.ofList, ResourcePool.singleton, Multiset.coe_replicate] using
      Addition.Gidney.gidneyComplement_eventCost width
  have body : ResourcePool.ofList
      ((Addition.Gidney.biFlipBodyGates width pivot).map (event .empty)) =
      (Addition.HRS.oneDirtyProgram width
        (Addition.Gidney.negatedPivot width pivot.val)).eventCost +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit) width := by
    rw [Addition.Gidney.biFlipBodyGates, List.map_append, ResourcePool.ofList_append,
      Addition.HRS.hrsOneDirtyGates_eventCost, complement]
  have bound := hrsOneDirty_native_bounds width (Addition.Gidney.negatedPivot width pivot.val)
  constructor
  · rw [list_x, body]
    simpa using Nat.add_le_add_right bound.1 width
  constructor
  · rw [list_c, body]
    simpa using bound.2.1
  · rw [list_t, body]
    simpa using bound.2.2
lemma biFlip_coordinate_bounds (width : Nat) (large : 3 ≤ width)
    (pivot : Fin (2 ^ width + 1)) :
    xCount (Addition.Gidney.biFlipGates width pivot) = 0 ∧
    cCount (Addition.Gidney.biFlipGates width pivot) ≤ oneDirtyXBound width + width ∧
    tCount (Addition.Gidney.biFlipGates width pivot) ≤
      oneDirtyCnotBound width + 4 * oneDirtyToffoliBound width := by
  have native : xCount (Addition.Gidney.biFlipGates width pivot) = 0 ∧
      cCount (Addition.Gidney.biFlipGates width pivot) =
        xCount (Addition.Gidney.biFlipBodyGates width pivot) ∧
      tCount (Addition.Gidney.biFlipGates width pivot) =
        cCount (Addition.Gidney.biFlipBodyGates width pivot) +
          4 * tCount (Addition.Gidney.biFlipBodyGates width pivot) := by
    have gateEq : Addition.Gidney.biFlipGates width pivot =
        Addition.Gidney.largeBiFlipGates width large pivot := by
      rw [Addition.Gidney.biFlipGates, dif_neg (show ¬width ≤ 2 by omega)]
    rw [gateEq]
    exact controlRightList_native_counts _ _ _ _ _ _ _
  have body := biFlipBody_bounds width pivot
  refine ⟨native.1, ?_, ?_⟩
  · rw [native.2.1]
    exact body.1
  · rw [native.2.2]
    exact Nat.add_le_add body.2.1 (Nat.mul_le_mul_left 4 body.2.2)
lemma comparison_coordinate_bounds (width : Nat) (pivot : Fin (2 ^ width + 1)) :
    xCount (Addition.Gidney.comparisonGates width pivot) ≤
      oneDirtyXBound (1 + width) + oneDirtyXBound width + 1 ∧
    cCount (Addition.Gidney.comparisonGates width pivot) ≤
      oneDirtyCnotBound (1 + width) + oneDirtyCnotBound width ∧
    tCount (Addition.Gidney.comparisonGates width pivot) ≤
      oneDirtyToffoliBound (1 + width) + oneDirtyToffoliBound width := by
  have extended := hrsOneDirty_native_bounds (1 + width)
    (Addition.Gidney.extendedNegatedPivot width pivot.val)
  have low := hrsOneDirty_native_bounds width (Addition.Gidney.pivotWord width pivot.val)
  constructor
  · rw [list_x, Addition.Gidney.gidneyComparisonGates_eventCost,
      Addition.Gidney.gidneyComparison_eventCost]
    split_ifs
    · simp
    · simpa using Nat.add_le_add_right (Nat.add_le_add extended.1 low.1) 1
  constructor
  · rw [list_c, Addition.Gidney.gidneyComparisonGates_eventCost,
      Addition.Gidney.gidneyComparison_eventCost]
    split_ifs
    · simp
    · simpa using Nat.add_le_add extended.2.1 low.2.1
  · rw [list_t, Addition.Gidney.gidneyComparisonGates_eventCost,
      Addition.Gidney.gidneyComparison_eventCost]
    split_ifs
    · simp
    · simpa using Nat.add_le_add extended.2.2 low.2.2
def twoPivotCnotBound (width : Nat) : Nat := 2 * (oneDirtyXBound width + width)
def twoPivotToffoliBound (width : Nat) : Nat :=
  2 * (oneDirtyCnotBound width + 4 * oneDirtyToffoliBound width) +
  2 * (oneDirtyXBound (1 + width) + oneDirtyXBound width + 1 +
    4 * (oneDirtyCnotBound (1 + width) + oneDirtyCnotBound width) +
    16 * (oneDirtyToffoliBound (1 + width) + oneDirtyToffoliBound width))
lemma twoPivot_coordinate_bounds (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (twoPivot outerWidth extra address selector pivot) = 0 ∧
    cCount (twoPivot outerWidth extra address selector pivot) ≤ twoPivotCnotBound (extra + 3) ∧
    tCount (twoPivot outerWidth extra address selector pivot) ≤
      twoPivotToffoliBound (extra + 3) := by
  rcases biFlip_coordinate_bounds (extra + 3) (by omega) pivot with ⟨bx, bc, bt⟩
  rcases comparison_coordinate_bounds (extra + 3) pivot with ⟨cx, cc, ct⟩
  rcases twoPivot_counts outerWidth extra address selector pivot with ⟨px, pc, pt⟩
  constructor
  · rw [px, bx, Nat.mul_zero]
  constructor
  · rw [pc]
    unfold twoPivotCnotBound
    omega
  · rw [pt]
    unfold twoPivotToffoliBound
    omega
end
noncomputable section
open Nat.FixedWidth EncodedBit GateSpec
lemma twoStage_coordinate_bounds (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    cCount (twoStage outerWidth extra address selector modulus constant) ≤
        3 * twoPivotCnotBound (extra + 3) ∧
      tCount (twoStage outerWidth extra address selector modulus constant) ≤
        3 * twoPivotToffoliBound (extra + 3) := by
  have first := twoPivot_coordinate_bounds outerWidth extra address selector
    (offsetFirstPivot modulus constant)
  have middle := twoPivot_coordinate_bounds outerWidth extra address selector modulus
  have last := twoPivot_coordinate_bounds outerWidth extra address selector
    (offsetLastPivot modulus constant)
  simp only [twoStage, cCount_append, tCount_append]
  constructor
  · have h := Nat.add_le_add (Nat.add_le_add first.2.1 middle.2.1) last.2.1
    omega
  · have h := Nat.add_le_add (Nat.add_le_add first.2.2 middle.2.2) last.2.2
    omega
lemma twoPrefix_coordinate_bounds (outerWidth extra : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (coefficient count : Nat)
    (within : count ≤ extra + 3) :
    cCount (twoPrefix outerWidth (extra + 3) address modulus coefficient count within) ≤
        count * (3 * twoPivotCnotBound (extra + 3)) ∧
      tCount (twoPrefix outerWidth (extra + 3) address modulus coefficient count within) ≤
        count * (3 * twoPivotToffoliBound (extra + 3)) := by
  induction count with
  | zero => constructor <;> exact Nat.zero_le _
  | succ index ih =>
      have before := ih (by omega)
      have head := twoStage_coordinate_bounds outerWidth extra address
        (⟨index, by omega⟩ : Fin (extra + 3)) modulus
        (accumulateConstant modulus coefficient index)
      simp only [twoPrefix, cCount_append, tCount_append]
      constructor
      · exact (Nat.add_le_add before.1 head.1).trans_eq (Nat.succ_mul _ _).symm
      · exact (Nat.add_le_add before.2 head.2).trans_eq (Nat.succ_mul _ _).symm
lemma twoGates_coordinate_bounds (outerWidth extra : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (coefficient : Nat) :
    cCount (twoGates outerWidth (extra + 3) address modulus coefficient) ≤
        (extra + 3) * (3 * twoPivotCnotBound (extra + 3)) ∧
      tCount (twoGates outerWidth (extra + 3) address modulus coefficient) ≤
        (extra + 3) * (3 * twoPivotToffoliBound (extra + 3)) := by
  exact twoPrefix_coordinate_bounds outerWidth extra address modulus coefficient
    (extra + 3) (Nat.le_refl _)
end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown
