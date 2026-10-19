/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources

/-!
# Independent native coordinates of the actual HRS recursion

Each selected constant bit is bounded by one in the existing carry formulas.
The three numerical recurrences use only the public width and retain the actual
bridge, ceiling/floor split and literal base instructions. They bound the same
program already accounted for in [HRS16, paper.tex:219-226,245].
-/

namespace QuantumAlg.MAU.Addition.HRS

/-- Width-only allowance for native X instructions in one carry. -/
def carryXBound : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 2 * ((n + 1) + n)
/-- Width-only allowance for native CNOT instructions in one carry. -/
def carryCnotBound : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 1) + n
/-- Width-only allowance for native Toffoli instructions in one carry. -/
def carryToffoliBound : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => 2 * n + 1 + (if n = 0 then 0 else 2 * (n - 1) + 1)
/-- The actual carry obeys all three independent native allowances. -/
lemma hrsCarry_native_bounds (width : Nat) (constant : Fin (2 ^ width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (carryProgram width constant).eventCost ≤ carryXBound width ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (carryProgram width constant).eventCost ≤ carryCnotBound width ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (carryProgram width constant).eventCost ≤ carryToffoliBound width := by
  have bit : (constant.val.testBit 0).toNat ≤ 1 := by
    cases constant.val.testBit 0 <;> decide
  cases width with
  | zero => simp [hrsCarry_native_count, carryXBound, carryCnotBound, carryToffoliBound]
  | succ width =>
    cases width with
    | zero =>
        simpa [hrsCarry_native_count, carryXBound, carryCnotBound, carryToffoliBound] using bit
    | succ n =>
      have first := hrsHighConstantCount_le constant.val (n + 1)
      have second := hrsHighConstantCount_le constant.val n
      constructor
      · rw [hrsCarry_x_count]
        dsimp only [carryXBound]
        omega
      constructor
      · rw [hrsCarry_cnot_count]
        dsimp only [carryCnotBound]
        omega
      · rw [hrsCarry_toffoli_count]
        dsimp only [carryToffoliBound]
        split_ifs <;> omega
/-- Native X allowance for the literal balanced constant-adder recursion. -/
def oneDirtyXBound (width : Nat) : Nat :=
  if base : width ≤ 1 then width else
    2 * carryXBound (lowWidth width) + oneDirtyXBound (lowWidth width) +
      oneDirtyXBound (highWidth width)
termination_by width
decreasing_by
  · exact (hrsSplit_decreases width (by omega)).1
  · exact (hrsSplit_decreases width (by omega)).2
/-- Native CNOT allowance for the literal balanced constant-adder recursion. -/
def oneDirtyCnotBound (width : Nat) : Nat :=
  if base : width ≤ 1 then 0 else
    6 * highWidth width + 2 * carryCnotBound (lowWidth width) +
      oneDirtyCnotBound (lowWidth width) + oneDirtyCnotBound (highWidth width)
termination_by width
decreasing_by
  · exact (hrsSplit_decreases width (by omega)).1
  · exact (hrsSplit_decreases width (by omega)).2
/-- Native Toffoli allowance for the literal balanced constant-adder recursion. -/
def oneDirtyToffoliBound (width : Nat) : Nat :=
  if base : width ≤ 1 then 0 else
    2 * (2 * highWidth width + 20 * (highWidth width - 1) +
      4 * (highWidth width - 2) + carryToffoliBound (lowWidth width)) +
      oneDirtyToffoliBound (lowWidth width) + oneDirtyToffoliBound (highWidth width)
termination_by width
decreasing_by
  · exact (hrsSplit_decreases width (by omega)).1
  · exact (hrsSplit_decreases width (by omega)).2
/-- One actual constant-adder program meets the three parameter-only recurrences. -/
lemma hrsOneDirty_native_bounds (width : Nat) (constant : Fin (2 ^ width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (oneDirtyProgram width constant).eventCost ≤ oneDirtyXBound width ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (oneDirtyProgram width constant).eventCost ≤ oneDirtyCnotBound width ∧
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (oneDirtyProgram width constant).eventCost ≤ oneDirtyToffoliBound width := by
  induction width using Nat.strong_induction_on with
  | h width ih =>
    by_cases base : width ≤ 1
    · constructor
      · simpa [hrsOneDirty_native_count, oneDirtyXBound, base] using
          EncodedBit.Word.constantOneIndices_length_le constant
      constructor
      · simp [hrsOneDirty_native_count, oneDirtyCnotBound, base]
      · simp [hrsOneDirty_native_count, oneDirtyToffoliBound, base]
    · have decrease := hrsSplit_decreases width (by omega)
      have low := ih (lowWidth width) decrease.1 ((splitWord width) constant).1
      have high := ih (highWidth width) decrease.2 ((splitWord width) constant).2
      have carry := hrsCarry_native_bounds (lowWidth width) ((splitWord width) constant).1
      rcases low with ⟨lx, lc, lt⟩
      rcases high with ⟨hx, hc, ht⟩
      rcases carry with ⟨cx, cc, ct⟩
      constructor
      · rw [hrsOneDirty_native_count, if_neg base, hrsRecursiveBridge_x_count]
        conv_rhs => rw [oneDirtyXBound]
        simp only [dif_neg base]
        omega
      constructor
      · rw [hrsOneDirty_native_count, if_neg base, hrsRecursiveBridge_cnot_count]
        conv_rhs => rw [oneDirtyCnotBound]
        simp only [dif_neg base]
        omega
      · rw [hrsOneDirty_native_count, if_neg base, hrsRecursiveBridge_toffoli_count]
        conv_rhs => rw [oneDirtyToffoliBound]
        simp only [dif_neg base]
        omega

/-- The three independent carry allowances fit the existing linear event envelope. -/
lemma hrsCarry_bounds_sum_le (width : Nat) :
    carryXBound width + carryCnotBound width + carryToffoliBound width ≤ 10 * width := by
  match width with
  | 0 => decide
  | 1 => decide
  | n + 2 =>
      simp only [carryXBound, carryCnotBound, carryToffoliBound]
      split_ifs <;> omega

/-- The sum of the independent coordinates obeys the original logarithmic envelope. -/
lemma hrsOneDirty_bounds_sum_le (width : Nat) :
    oneDirtyXBound width + oneDirtyCnotBound width + oneDirtyToffoliBound width ≤
      width * (39 * Nat.clog 2 width + 1) := by
  have bounded := hrsBalancedRecurrence_bound
    (fun w _ => oneDirtyXBound w + oneDirtyCnotBound w + oneDirtyToffoliBound w)
  apply bounded ?_ ?_ width ⟨0, Nat.two_pow_pos width⟩
  · intro w base constant
    simp [oneDirtyXBound, oneDirtyCnotBound, oneDirtyToffoliBound, base]
  · intro w two constant
    have base : ¬w ≤ 1 := by omega
    have carry := hrsCarry_bounds_sum_le (lowWidth w)
    have balanced := (hrsSplit_capacity w).2.1
    have total := hrsSplit_width_sum w
    conv_lhs =>
      rw [oneDirtyXBound, oneDirtyCnotBound, oneDirtyToffoliBound]
    simp only [dif_neg base]
    omega

end QuantumAlg.MAU.Addition.HRS
