/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Controlled.Coordinates
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Counts
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

/-!
# Actual zero-X and independent CNOT bounds for the two-control accumulator

The actual BCBC construction retains both borrowed bits and every
external word coordinate [G17, paper.tex:276-293,319-334]. Native
coordinates and serial time belong to this same emitted program.
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

noncomputable section

open Nat.FixedWidth BinaryLabelEncoding EncodedBit GateSpec

/-- Literal control expansion emits no X and converts the source X count to CNOT. -/
lemma originalControlled_native_counts (outerWidth width : Nat)
    (address : Fin outerWidth) (body : List (GateSpec (encoding width))) :
    xCount (originalControlled outerWidth width address body) = 0 ∧
      cCount (originalControlled outerWidth width address body) = xCount body := by
  by_cases small : width ≤ 1
  · simp only [originalControlled, dif_pos small, xCount, cCount, List.map_map,
      Function.comp_def, controlSmall_xMultiplicity, controlSmall_cnotMultiplicity]
    simp
  · simp only [originalControlled, dif_neg small]
    exact ⟨(outerControl_counts outerWidth width (by omega) address body).1,
      (outerControl_counts outerWidth width (by omega) address body).2.1⟩

/-- The true bi-flip zero-X law survives both external placements. -/
lemma twoPivot_xCount (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    xCount (twoPivot outerWidth extra address selector pivot) = 0 := by
  rw [(twoPivot_counts outerWidth extra address selector pivot).1,
    biFlip_xCount, Nat.mul_zero]

/-- The three actual two-control pivots contain no X instructions. -/
lemma twoStage_xCount (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    xCount (twoStage outerWidth extra address selector modulus constant) = 0 := by
  simp only [twoStage, xCount_append, twoPivot_xCount, Nat.zero_add]

/-- Every width-complete controlled stage has zero actual X count. -/
lemma twoStageGates_xCount (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (selector : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    xCount (twoStageGates outerWidth width address selector modulus constant) = 0
  | 0, _, selector, _, _ => Fin.elim0 selector
  | 1, address, _selector, _modulus, _constant =>
      (originalControlled_native_counts outerWidth 1 address _).1
  | 2, address, _selector, _modulus, _constant =>
      (originalControlled_native_counts outerWidth 2 address _).1
  | extra + 3, address, selector, modulus, constant =>
      twoStage_xCount outerWidth extra address selector modulus constant

/-- The ordered prefix has zero X count on the same emitted list. -/
lemma twoPrefix_xCount (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    xCount (twoPrefix outerWidth width address modulus coefficient count within) = 0 := by
  induction count with
  | zero => rfl
  | succ index ih =>
      rw [twoPrefix, xCount_append, ih (by omega), twoStageGates_xCount, Nat.zero_add]

/-- The complete actual two-control accumulator has zero X count at every width. -/
lemma twoGates_xCount (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (modulus : Fin (2 ^ width + 1)) → (coefficient : Nat) →
    xCount (twoGates outerWidth width address modulus coefficient) = 0
  | 0, address, _modulus, _coefficient =>
      (originalControlled_native_counts outerWidth 0 address _).1
  | 1, address, _modulus, _coefficient =>
      (originalControlled_native_counts outerWidth 1 address _).1
  | 2, address, _modulus, _coefficient =>
      (originalControlled_native_counts outerWidth 2 address _).1
  | extra + 3, address, modulus, coefficient =>
      twoPrefix_xCount outerWidth (extra + 3) address modulus coefficient
        (extra + 3) (Nat.le_refl _)

/-- Each actual two-control pivot obeys its separate CNOT allowance. -/
lemma twoPivot_cCount_bound (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (pivot : Fin (2 ^ (extra + 3) + 1)) :
    cCount (twoPivot outerWidth extra address selector pivot) ≤
      twoPivotCnotBound (extra + 3) :=
  (twoPivot_coordinate_bounds outerWidth extra address selector pivot).2.1

/-- The independent CNOT cap is zero on the unchanged small paths. -/
def twoStageCnotBound (width : Nat) : Nat :=
  if width ≤ 2 then 0 else
    3 * twoPivotCnotBound width

/-- The actual two-control stage meets the sum of its three bi-flip CNOT caps. -/
lemma twoStage_cCount_bound (outerWidth extra : Nat) (address : Fin outerWidth)
    (selector : Fin (extra + 3)) (modulus : Fin (2 ^ (extra + 3) + 1))
    (constant : Fin (modulus.val + 1)) :
    cCount (twoStage outerWidth extra address selector modulus constant) ≤
      twoStageCnotBound (extra + 3) := by
  have first := twoPivot_cCount_bound outerWidth extra address selector
    (offsetFirstPivot modulus constant)
  have middle := twoPivot_cCount_bound outerWidth extra address selector modulus
  have last := twoPivot_cCount_bound outerWidth extra address selector
    (offsetLastPivot modulus constant)
  simp only [twoStage, cCount_append, twoStageCnotBound,
    if_neg (show ¬extra + 3 ≤ 2 by omega)]
  omega

/-- The source stage's zero-X count follows from its actual compiled program ledger. -/
private lemma sourceStage_xCount (width : Nat) (selector : Fin width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    xCount (Gidney.stageGates width selector modulus constant) = 0 := by
  change ((Gidney.stageGates width selector modulus constant).map xMultiplicity).sum = 0
  rw [← programList_x_count_eq_sum (QubitLayout.canonical _) .empty,
    programList_eventCost, gidneyStageGates_eventCost]
  exact gidneyStage_singleQubit_count width selector modulus constant

/-- The width-complete stage obeys the independent CNOT cap, including literal small bases. -/
lemma twoStageGates_cCount_bound (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (selector : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    cCount (twoStageGates outerWidth width address selector modulus constant) ≤
      twoStageCnotBound width
  | 0, _, selector, _, _ => Fin.elim0 selector
  | 1, address, selector, modulus, constant => by
      rw [twoStageGates, (originalControlled_native_counts outerWidth 1 address _).2,
        sourceStage_xCount]
      exact Nat.zero_le _
  | 2, address, selector, modulus, constant => by
      rw [twoStageGates, (originalControlled_native_counts outerWidth 2 address _).2,
        sourceStage_xCount]
      exact Nat.zero_le _
  | extra + 3, address, selector, modulus, constant =>
      twoStage_cCount_bound outerWidth extra address selector modulus constant

/-- The exact ordered stage list meets the sum of independent per-stage CNOT allowances. -/
lemma twoPrefix_cCount_bound (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    cCount (twoPrefix outerWidth width address modulus coefficient count within) ≤
      count * twoStageCnotBound width := by
  induction count with
  | zero => simp only [twoPrefix, cCount, List.map_nil, List.sum_nil, Nat.zero_mul, Nat.le_refl]
  | succ index ih =>
      rw [twoPrefix, cCount_append, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (twoStageGates_cCount_bound _ _ _ _ _ _)

/-- Small complete paths have no CNOT because the original accumulator has no native X. -/
private lemma originalControlled_accumulate_cCount (outerWidth width : Nat)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    cCount (originalControlled outerWidth width address
      (Gidney.gates width modulus coefficient)) = 0 := by
  rw [(originalControlled_native_counts outerWidth width address _).2]
  exact gidneyAccumulateGates_xMultiplicity_sum width modulus coefficient

/-- The complete actual accumulator meets a width-only CNOT allowance at every modulus. -/
lemma twoGates_cCount_bound (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (modulus : Fin (2 ^ width + 1)) → (coefficient : Nat) →
    cCount (twoGates outerWidth width address modulus coefficient) ≤
      width * twoStageCnotBound width
  | 0, address, modulus, coefficient => by
      simp only [twoGates, originalControlled_accumulate_cCount, Nat.zero_mul, Nat.le_refl]
  | 1, address, modulus, coefficient => by
      simp [twoGates, originalControlled_accumulate_cCount, twoStageCnotBound]
  | 2, address, modulus, coefficient => by
      simp [twoGates, originalControlled_accumulate_cCount, twoStageCnotBound]
  | extra + 3, address, modulus, coefficient =>
      twoPrefix_cCount_bound outerWidth (extra + 3) address modulus coefficient
        (extra + 3) (Nat.le_refl _)

/-- The same actual program ledger has zero X and the independent CNOT cap. -/
lemma twoAccumulator_native_counts (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (twoProgram outerWidth width address modulus coefficient).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (twoProgram outerWidth width address modulus coefficient).eventCost ≤
          width * twoStageCnotBound width := by
  constructor
  · rw [twoProgram, programList_x_count_eq_sum]
    exact twoGates_xCount outerWidth width address modulus coefficient
  · rw [twoProgram, programList_cnot_count_eq_sum]
    exact twoGates_cCount_bound outerWidth width address modulus coefficient

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney.ControlPushdown
