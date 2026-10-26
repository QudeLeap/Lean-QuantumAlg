/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty.Resources

/-!
# Exact numerical native-coordinate recursion for the unchanged HRS word

This helper evaluates only independent numerical recurrences. Each term
is proved from the actual one-dirty program, its real ceiling/floor split,
and its complete native bridge. Every compile-time constant half remains
in the recursion, including the literal zero- and one-width bases.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

open Addition.HRS

/-- Numerical carry ledger, with the selected high constant bits retained exactly. -/
def carryCount (width constant : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  match width with
  | 0 => 0
  | 1 => (constant.testBit 0).toNat * (if .gate .cnot = focus then 1 else 0)
  | n + 2 =>
      (highConstantCount constant (n + 1) + highConstantCount constant n) *
        ((if .gate .cnot = focus then 1 else 0) +
          2 * (if .gate .singleQubit = focus then 1 else 0)) +
        (2 * n + (constant.testBit 0).toNat +
          (if n = 0 then 0 else 2 * (n - 1) + (constant.testBit 0).toNat)) *
          (if .gate .toffoli = focus then 1 else 0)

private lemma carryCount_eq (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (carryProgram width constant).eventCost =
      carryCount width constant.val focus := by
  cases width with
  | zero => rw [hrsCarry_native_count]; rfl
  | succ previous =>
      cases previous with
      | zero => rw [hrsCarry_native_count]; rfl
      | succ tail => rw [hrsCarry_native_count]; rfl

/-- Numerical ledger of the actual four-Toffoli-lowered controlled increment. -/
def incrementCount (width : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  2 * width * (if .gate .cnot = focus then 1 else 0) +
    (2 * width + 20 * (width - 1) + 4 * (width - 2)) *
      (if .gate .toffoli = focus then 1 else 0)

/-- Each numerical term counts one actual bridge or one actual recursive child word. -/
def oneDirtyCount (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  if base : width ≤ 1 then
    (EncodedBit.Word.constantOneIndices constant).length *
      (if .gate .singleQubit = focus then 1 else 0)
  else
    2 * (incrementCount (highWidth width) focus +
      highWidth width * (if .gate .cnot = focus then 1 else 0) +
        carryCount (lowWidth width) ((splitWord width) constant).1.val focus) +
      oneDirtyCount (lowWidth width) ((splitWord width) constant).1 focus +
      oneDirtyCount (highWidth width) ((splitWord width) constant).2 focus
termination_by width
decreasing_by
  · exact (hrsSplit_decreases width (by omega)).1
  · exact (hrsSplit_decreases width (by omega)).2

/-- This numerical recursion equals each coordinate of the same executed native HRS program. -/
lemma oneDirtyCount_eq (width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (oneDirtyProgram width constant).eventCost =
      oneDirtyCount width constant focus := by
  induction width using Nat.strong_induction_on with
  | h width inductionHypothesis =>
      by_cases base : width ≤ 1
      · rw [hrsOneDirty_native_count, if_pos base]
        conv_rhs => rw [oneDirtyCount]
        rw [dif_pos base]
      · have decrease := hrsSplit_decreases width (by omega)
        rw [hrsOneDirty_native_count, if_neg base, hrsRecursiveBridge_native_count,
          hrsControlledBorrowedIncrement_native_count, carryCount_eq,
          inductionHypothesis _ decrease.1, inductionHypothesis _ decrease.2]
        conv_rhs => rw [oneDirtyCount]
        rw [dif_neg base]
        rfl

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
