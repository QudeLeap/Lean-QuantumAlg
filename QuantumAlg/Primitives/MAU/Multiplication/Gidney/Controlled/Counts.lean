/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Controlled
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled.Counts
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Counts.Values
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Independent native coordinates and time for selected unit multiplication

The actual BCBC construction retains both borrowed bits and every
external word coordinate [G17, paper.tex:276-293,319-334]. Native
coordinates and serial time belong to this same emitted program.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Accumulate.Gidney Nat.FixedWidth EncodedBit GateSpec
open Accumulate.Gidney.ControlPushdown

/-- A reversed native list has the same actual X multiplicity. -/
private lemma xCount_reverse {Data : Type} {carrier : BinaryLabelEncoding Data}
    (body : List (GateSpec carrier)) :
    ControlPushdown.xCount body.reverse = ControlPushdown.xCount body := by
  simp only [ControlPushdown.xCount, List.map_reverse, List.sum_reverse]

/-- A reversed native list has the same actual CNOT multiplicity. -/
private lemma cCount_reverse {Data : Type} {carrier : BinaryLabelEncoding Data}
    (body : List (GateSpec carrier)) :
    ControlPushdown.cCount body.reverse = ControlPushdown.cCount body := by
  simp only [ControlPushdown.cCount, List.map_reverse, List.sum_reverse]

/-- Actual external control of the literal swap produces no X or CNOT instructions. -/
private lemma controlledSwap_native_counts (outerWidth width : Nat)
    (address : Fin outerWidth) :
    ControlPushdown.xCount
        (ControlPushdown.originalControlled outerWidth width address (wordSwapGates width)) = 0 ∧
      ControlPushdown.cCount
        (ControlPushdown.originalControlled outerWidth width address
          (wordSwapGates width)) = 0 := by
  have counts := ControlPushdown.originalControlled_native_counts outerWidth width address
    (wordSwapGates width)
  exact ⟨counts.1, counts.2.trans (wordSwapGates_xMultiplicity_sum width)⟩

/-- No actual controlled multiplier gate is a single-qubit instruction. -/
lemma gidneyControlledUnitMultiplication_xCount (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ControlPushdown.xCount (controlledGates outerWidth width address modulus coefficient) = 0 := by
  by_cases small : width ≤ 2
  · rw [controlledGates, dif_pos small]
    exact (ControlPushdown.originalControlled_native_counts outerWidth width address _).1
  · simp only [controlledGates, dif_neg small, ControlPushdown.xCount_append, xCount_reverse,
      ControlPushdown.twoGates_xCount, (controlledSwap_native_counts outerWidth width address).1,
      Nat.zero_add]

/-- The exact large-width CNOT ledger contains both MAC ledgers and no selected-swap CNOT. -/
lemma gidneyControlledUnitMultiplication_cCount_large (outerWidth width : Nat)
    (large : ¬width ≤ 2) (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ControlPushdown.cCount (controlledGates outerWidth width address modulus coefficient) =
      ControlPushdown.cCount (ControlPushdown.twoGates outerWidth width address modulus
        (coefficient : ZMod modulus.val).val) +
      ControlPushdown.cCount (ControlPushdown.twoGates outerWidth width address modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val) := by
  simp only [controlledGates, dif_neg large, ControlPushdown.cCount_append, cCount_reverse,
    (controlledSwap_native_counts outerWidth width address).2, Nat.add_zero]

/-- Two width-complete MAC allowances give an independent selected-multiplier CNOT budget. -/
def controlledCnotBound (width : Nat) : Nat :=
  2 * (width * ControlPushdown.twoStageCnotBound width)

/-- The unchanged small path and the actual two-MAC construction have one Toffoli allowance. -/
def controlledToffoliBound (width : Nat) : Nat :=
  if width ≤ 2 then 4 * eventBound width else
    2 * (width * (3 * ControlPushdown.twoPivotToffoliBound width)) + 3 * width

/-- Serial arithmetic time is the sum of the two nonzero native coordinate allowances. -/
def controlledTimeBound (width : Nat) : Nat :=
  controlledCnotBound width + controlledToffoliBound width

/-- The actual selected multiplier meets the independent CNOT budget on its full original domain. -/
lemma gidneyControlledUnitMultiplication_cCount_bound (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ControlPushdown.cCount (controlledGates outerWidth width address modulus coefficient) ≤
      controlledCnotBound width := by
  by_cases small : width ≤ 2
  · rw [controlledGates, dif_pos small,
      (ControlPushdown.originalControlled_native_counts outerWidth width address _).2]
    have zero : ControlPushdown.xCount (gates width modulus coefficient) = 0 :=
      gidneyUnitMultiplicationGates_xMultiplicity_sum width modulus coefficient
    rw [zero]
    exact Nat.zero_le _
  · rw [gidneyControlledUnitMultiplication_cCount_large outerWidth width small address]
    have forward := ControlPushdown.twoGates_cCount_bound outerWidth width address modulus
      (coefficient : ZMod modulus.val).val
    have inverse := ControlPushdown.twoGates_cCount_bound outerWidth width address modulus
      ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
    unfold controlledCnotBound
    omega

/-- The same actual selected program has zero X count and its independent CNOT allowance. -/
lemma gidneyControlledUnitMultiplication_native_counts (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (controlledProgram outerWidth width address modulus coefficient).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (controlledProgram outerWidth width address modulus coefficient).eventCost ≤
          controlledCnotBound width := by
  constructor
  · rw [controlledProgram, programList_x_count_eq_sum]
    exact gidneyControlledUnitMultiplication_xCount outerWidth width address modulus coefficient
  · rw [controlledProgram, programList_cnot_count_eq_sum]
    exact gidneyControlledUnitMultiplication_cCount_bound
      outerWidth width address modulus coefficient

private lemma tCount_reverse {Data : Type} {carrier : BinaryLabelEncoding Data}
    (body : List (GateSpec carrier)) : tCount body.reverse = tCount body := by
  simp only [tCount, List.map_reverse, List.sum_reverse]
private lemma controlledSwap_toffoli_count (outerWidth width : Nat) (large : 3 ≤ width)
    (address : Fin outerWidth) :
    cCount (originalControlled outerWidth width address (wordSwapGates width)) = 0 ∧
      tCount (originalControlled outerWidth width address (wordSwapGates width)) =
        3 * width := by
  rw [originalControlled, dif_neg (show ¬width ≤ 1 by omega)]
  have cnots : cCount (wordSwapGates width) = 3 * width :=
    EncodedBit.Word.swapGates_cnotMultiplicity_sum _ _ _
  have old := length_eq_multiplicity_sums (wordSwapGates width)
  change (wordSwapGates width).length = xCount (wordSwapGates width) +
    cCount (wordSwapGates width) + tCount (wordSwapGates width) at old
  rw [gidneyWordSwap_gate_count, cnots] at old
  have zeroX : xCount (wordSwapGates width) = 0 := by omega
  have zeroT : tCount (wordSwapGates width) = 0 := by omega
  have counts := outerControl_counts outerWidth width (by omega) address (wordSwapGates width)
  constructor
  · exact counts.2.1.trans zeroX
  · rw [counts.2.2, cnots, zeroT, Nat.mul_zero, Nat.add_zero]

/-- The actual large-width gate list meets its separate CNOT and Toffoli allowances. -/
lemma gidneyControlledUnitMultiplication_coordinate_bounds_large (outerWidth width : Nat)
    (large : 3 ≤ width)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    cCount (controlledGates outerWidth width address modulus coefficient) ≤
        controlledCnotBound width ∧
      tCount (controlledGates outerWidth width address modulus coefficient) ≤
        controlledToffoliBound width := by
  obtain ⟨extra, rfl⟩ : ∃ extra, width = extra + 3 := ⟨width - 3, by omega⟩
  obtain ⟨fc, ft⟩ := ControlPushdown.twoGates_coordinate_bounds
    outerWidth extra address modulus (coefficient : ZMod modulus.val).val
  obtain ⟨ic, it⟩ := ControlPushdown.twoGates_coordinate_bounds
    outerWidth extra address modulus
    ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
  have swap := controlledSwap_toffoli_count outerWidth (extra + 3) (by omega) address
  simp only [controlledGates, dif_neg (show ¬extra + 3 ≤ 2 by omega),
    cCount_append, tCount_append, cCount_reverse, tCount_reverse,
    swap.1, swap.2, Nat.add_zero]
  simp only [controlledCnotBound, controlledToffoliBound,
    ControlPushdown.twoStageCnotBound, if_neg (show ¬extra + 3 ≤ 2 by omega)]
  constructor <;> omega

/-- The same actual program meets all three native coordinate allowances at every width. -/
lemma gidneyControlledUnitMultiplication_native_bounds (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (controlledProgram outerWidth width address modulus coefficient).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (controlledProgram outerWidth width address modulus coefficient).eventCost ≤
          controlledCnotBound width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (controlledProgram outerWidth width address modulus coefficient).eventCost ≤
          controlledToffoliBound width := by
  have existing := gidneyControlledUnitMultiplication_native_counts
    outerWidth width address modulus coefficient
  refine ⟨existing.1, existing.2, ?_⟩
  rw [controlledProgram, programList_toffoli_count_eq_sum]
  by_cases small : width ≤ 2
  · have lengthBound := gidneyControlledUnitMultiplication_length_bound
      outerWidth width address modulus coefficient
    have coordinates := length_eq_multiplicity_sums
      (controlledGates outerWidth width address modulus coefficient)
    simp only [controlledToffoliBound, if_pos small]
    omega
  · exact (gidneyControlledUnitMultiplication_coordinate_bounds_large
      outerWidth width (by omega) address modulus coefficient).2

/-- Unit duration of the actual serial list is exactly its CNOT plus Toffoli count. -/
lemma gidneyControlledUnitMultiplication_unitDepth_eq_counts (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (controlledProgram outerWidth width address modulus coefficient).evaluatedEventDepth
        (fun _ => 1) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
          (controlledProgram outerWidth width address modulus coefficient).eventCost +
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (controlledProgram outerWidth width address modulus coefficient).eventCost := by
  have zero := (gidneyControlledUnitMultiplication_native_counts
    outerWidth width address modulus coefficient).1
  calc
    _ = (controlledGates outerWidth width address modulus coefficient).length := by
      rw [controlledProgram, programList_evaluatedEventDepth_unit]
    _ = primitiveEventCount
        (controlledProgram outerWidth width address modulus coefficient) := by
      rw [controlledProgram, primitiveEventCount_programList]
    _ = _ := by simp only [primitiveEventCount, zero, Nat.zero_add]

/-- The actual selected program meets its independent serial-time allowance. -/
lemma gidneyControlledUnitMultiplication_time_bound (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    (controlledProgram outerWidth width address modulus coefficient).evaluatedEventDepth
        (fun _ => 1) ≤ controlledTimeBound width := by
  rw [gidneyControlledUnitMultiplication_unitDepth_eq_counts]
  have bounds := gidneyControlledUnitMultiplication_native_bounds
    outerWidth width address modulus coefficient
  exact Nat.add_le_add bounds.2.1 bounds.2.2

/-- Each coordinate is bounded by their independently specified serial sum. -/
lemma controlledCnotBound_le_timeBound (width : Nat) :
    controlledCnotBound width ≤ controlledTimeBound width := Nat.le_add_right _ _

/-- Each coordinate is bounded by their independently specified serial sum. -/
lemma controlledToffoliBound_le_timeBound (width : Nat) :
    controlledToffoliBound width ≤ controlledTimeBound width := Nat.le_add_left _ _

/-- The refined CNOT allowance also satisfies the original logarithmic CNOT envelope. -/
lemma controlledCnotBound_le_logarithmic (width : Nat) :
    controlledCnotBound width ≤
      12 * width * (Addition.Gidney.constantOffsetEventBound width + width) := by
  have total := Addition.HRS.hrsOneDirty_bounds_sum_le width
  simp only [controlledCnotBound, ControlPushdown.twoStageCnotBound]
  split_ifs
  · simp
  · have coordinate : Addition.HRS.oneDirtyXBound width ≤
        Addition.Gidney.constantOffsetEventBound width := by
      unfold Addition.Gidney.constantOffsetEventBound
      omega
    have scaled := Nat.mul_le_mul_left (12 * width) (Nat.add_le_add_right coordinate width)
    calc
      _ = 12 * width * (Addition.HRS.oneDirtyXBound width + width) := by
        unfold ControlPushdown.twoPivotCnotBound
        ring
      _ ≤ _ := scaled

/-- The refined numerical allowance fits the existing total-event envelope without clipping. -/
lemma controlledTimeBound_le_eventBound (width : Nat) :
    controlledTimeBound width ≤ 4 * eventBound width := by
  by_cases small : width ≤ 2
  · simp [controlledTimeBound, controlledCnotBound, controlledToffoliBound,
      ControlPushdown.twoStageCnotBound, small]
  · have first := Addition.HRS.hrsOneDirty_bounds_sum_le width
    have next := Addition.HRS.hrsOneDirty_bounds_sum_le (1 + width)
    have inner :
        2 * Addition.HRS.oneDirtyXBound width + 5 * Addition.HRS.oneDirtyCnotBound width +
          20 * Addition.HRS.oneDirtyToffoliBound width +
          Addition.HRS.oneDirtyXBound (1 + width) +
          4 * Addition.HRS.oneDirtyCnotBound (1 + width) +
          16 * Addition.HRS.oneDirtyToffoliBound (1 + width) + width + 1 ≤
        20 * Addition.Gidney.constantOffsetEventBound width +
          16 * Addition.Gidney.constantOffsetEventBound (1 + width) + width + 1 := by
      unfold Addition.Gidney.constantOffsetEventBound
      omega
    have scaled := Nat.mul_le_mul_left (12 * width) inner
    have refined : controlledTimeBound width ≤
        240 * width * Addition.Gidney.constantOffsetEventBound width +
          192 * width * Addition.Gidney.constantOffsetEventBound (1 + width) +
          12 * width ^ 2 + 15 * width := by
      simp only [controlledTimeBound, controlledCnotBound, controlledToffoliBound,
        ControlPushdown.twoStageCnotBound, if_neg small,
        ControlPushdown.twoPivotCnotBound, ControlPushdown.twoPivotToffoliBound]
      nlinarith
    unfold eventBound Accumulate.Gidney.stageEventBound
    rw [if_neg small]
    unfold Addition.Gidney.modularOffsetEventBound Addition.Gidney.pivotEventBound
      Addition.Gidney.biFlipEventBound Addition.Gidney.comparisonEventBound
    nlinarith

/-- Kernel-checked native and serial-time allowances for one 2048-bit selected multiplier. -/
lemma controlledBounds_2048 :
    controlledCnotBound 2048 = 1812234240 ∧
      controlledToffoliBound 2048 = 509612759040 ∧
      controlledTimeBound 2048 = 511424993280 := by
  have word := Addition.HRS.hrsOneDirty_bounds_2048
  have extended := Addition.HRS.hrsOneDirty_bounds_2049
  norm_num [controlledCnotBound, controlledToffoliBound, controlledTimeBound,
    ControlPushdown.twoStageCnotBound, ControlPushdown.twoPivotCnotBound,
    ControlPushdown.twoPivotToffoliBound, word.1, word.2.1, word.2.2,
    extended.1, extended.2.1, extended.2.2]

end

end QuantumAlg.MAU.Multiplication.Gidney
