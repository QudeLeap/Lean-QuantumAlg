/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Bridge.Program
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Resources
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources

/-!
# Literal native resources of the recursive HRS bridge

The formulas count the actual six component programs. In particular the
controlled incrementer's four-Toffoli lowering is retained, rather than
replaced by the distinct optimized estimate in the source
[HRS16, paper.tex:219-226,245]. The resulting bound is `39 * width` events
per bridge on a ceiling/floor split.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- The selected high-constant-bit count cannot exceed the number of positions. -/
theorem hrsHighConstantCount_le (constant count : Nat) :
    highConstantCount constant count ≤ count := by
  induction count with
  | zero => simp [highConstantCount]
  | succ count ih =>
      have hbit : (constant.testBit (count + 1)).toNat ≤ 1 := by
        cases constant.testBit (count + 1) <;> decide
      simp only [highConstantCount]
      omega

/-- The literal controlled incrementer has at most 28 events per target bit. -/
theorem hrsControlledBorrowedIncrement_event_count_le (width : Nat) :
    (controlledBorrowedIncrementProgram width).eventCost.card ≤ 28 * width := by
  rw [hrsControlledBorrowedIncrement_event_count]
  omega

/-- All-width upper bound derived from the actual carry list's selected-bit formula. -/
theorem hrsCarry_event_count_le (width : Nat) (constant : Fin (2 ^ width)) :
    (carryProgram width constant).eventCost.card ≤ 10 * width := by
  have hbit : (constant.val.testBit 0).toNat ≤ 1 := by
    cases constant.val.testBit 0 <;> decide
  rw [hrsCarry_event_count]
  match width with
  | 0 => simp
  | 1 =>
      change (constant.val.testBit 0).toNat ≤ 10
      omega
  | n + 2 =>
      change 3 * (highConstantCount constant.val (n + 1) + highConstantCount constant.val n) +
          2 * n + (constant.val.testBit 0).toNat +
          (if n = 0 then 0 else 2 * (n - 1) + (constant.val.testBit 0).toNat) ≤ 10 * (n + 2)
      have hforward := hrsHighConstantCount_le constant.val (n + 1)
      have hbackward := hrsHighConstantCount_le constant.val n
      split_ifs <;> omega

/-- X gates occur only in the two actual carry components. -/
theorem hrsRecursiveBridge_x_count (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (recursiveBridgeProgram width constant).eventCost =
      2 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit)
        (carryProgram (lowWidth width) constant).eventCost := by
  rw [hrsRecursiveBridge_native_count, hrsControlledBorrowedIncrement_x_count]
  simp

/-- Two increments and two high-word complements supply six CNOTs per high bit. -/
theorem hrsRecursiveBridge_cnot_count (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (recursiveBridgeProgram width constant).eventCost =
      6 * highWidth width + 2 * ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (carryProgram (lowWidth width) constant).eventCost := by
  rw [hrsRecursiveBridge_native_count, hrsControlledBorrowedIncrement_cnot_count]
  simp only [ite_true, Nat.mul_one]
  omega

/-- Every Toffoli is inherited from the lowered increment or the actual carry. -/
theorem hrsRecursiveBridge_toffoli_count (width : Nat) (constant : Fin (2 ^ lowWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (recursiveBridgeProgram width constant).eventCost =
      2 * (2 * highWidth width + 20 * (highWidth width - 1) +
        4 * (highWidth width - 2) + ResourcePool.count
          (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (carryProgram (lowWidth width) constant).eventCost) := by
  rw [hrsRecursiveBridge_native_count, hrsControlledBorrowedIncrement_toffoli_count]
  simp

/-- Balanced widths sharpen the actual linear bridge bound to 39 events per input bit. -/
theorem hrsRecursiveBridge_event_count_le (width : Nat)
    (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).eventCost.card ≤ 39 * width := by
  rw [hrsRecursiveBridge_event_count]
  have hincrement := hrsControlledBorrowedIncrement_event_count_le (highWidth width)
  have hcarry := hrsCarry_event_count_le (lowWidth width) constant
  have hsum := hrsSplit_width_sum width
  have hbalanced := (hrsSplit_capacity width).2.1
  omega

/-- This actual bridge is serial; its unit depth equals its event count. -/
theorem hrsRecursiveBridge_depth_eq_events (width : Nat)
    (constant : Fin (2 ^ lowWidth width)) :
    (recursiveBridgeProgram width constant).evaluatedEventDepth (fun _ => 1) =
      (recursiveBridgeProgram width constant).eventCost.card := by
  simp only [hrsRecursiveBridge_serial_depth, hrsRecursiveBridge_event_count,
    hrsControlledBorrowedIncrement_serial_depth, hrsControlledBorrowedIncrement_event_count,
    hrsCarry_serial_depth]

end

end QuantumAlg.MAU.Addition.HRS
