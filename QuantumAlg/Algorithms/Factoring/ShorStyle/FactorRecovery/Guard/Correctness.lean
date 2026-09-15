/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Arithmetic
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Arithmetic

/-!
# The real stored-order guard has the original source decision

Each comparison below is read from the actual intermediate store. The zero
operand comes from self-XOR, evenness from the last physical bit, positivity
from the native word comparison, and acceptance from the real decoded tag.
The enclosing workspace discharges the physical separation conditions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Actual write/read separation required by the five native guard instructions. -/
structure GuardSeparation (cells : Cells ctx N) : Prop where
  zeroExpanded : cells.zero.key ≠ cells.expanded.key
  activeExpanded : cells.active.key ≠ cells.expanded.key
  positiveExpanded : cells.positive.key ≠ cells.expanded.key
  activeZero : cells.active.key ≠ cells.zero.key
  positiveActive : cells.positive.key ≠ cells.active.key

private theorem and_toBool (left right : CShape.Value .bit) :
    (Resource.BitOpcode.eval .and (.product left right)).toBool =
      (left.toBool && right.toBool) := by
  cases left
  cases right
  rfl

/-- The actual final guard bit is the conjunction of the original three stored decisions. -/
theorem guard_result (cells : Cells ctx N) (store : Store ctx)
    (separate : GuardSeparation cells) :
    ((guardStore cells store).read (activeRead cells)).toBool =
      ((decide (Even (store.read (orderRead cells)).toNat) &&
        decide (0 < (store.read (orderRead cells)).toNat)) &&
          (store.read (expandedRead cells)).first.toBool) := by
  let cleared := store.applyOp (clearZeroOp cells)
  let even := cleared.applyOp (evenOrderOp cells)
  let positive := even.applyOp (positiveOrderOp cells)
  let combined := positive.applyOp (positiveEvenOp cells)
  have clearedExpanded : cleared.read (expandedRead cells) =
      store.read (expandedRead cells) :=
    Store.read_applyOp_of_not_mem_storageKeys store (clearZeroOp cells) (expandedRead cells)
      (fun member => separate.zeroExpanded (List.mem_singleton.mp member))
  have evenExpanded : even.read (expandedRead cells) = store.read (expandedRead cells) :=
    (Store.read_applyOp_of_not_mem_storageKeys cleared (evenOrderOp cells) (expandedRead cells)
      (fun member => separate.activeExpanded (List.mem_singleton.mp member))).trans clearedExpanded
  have positiveExpanded : positive.read (expandedRead cells) =
      store.read (expandedRead cells) :=
    (Store.read_applyOp_of_not_mem_storageKeys even (positiveOrderOp cells) (expandedRead cells)
      (fun member => separate.positiveExpanded (List.mem_singleton.mp member))).trans evenExpanded
  have combinedExpanded : combined.read (expandedRead cells) =
      store.read (expandedRead cells) :=
    (Store.read_applyOp_of_not_mem_storageKeys positive (positiveEvenOp cells)
      (expandedRead cells)
      (fun member => separate.activeExpanded (List.mem_singleton.mp member))).trans positiveExpanded
  have clearedZero : (cleared.read (.storage cells.zero.toCStorageRef)).toNat = 0 :=
    (congrArg CShape.Value.toNat (Store.read_applyOp_output store (clearZeroOp cells))).trans
      (NativeAdjacentWord.selfXor_toNat (store.read (.storage cells.zero.toCStorageRef)))
  have evenZero : (even.read (.storage cells.zero.toCStorageRef)).toNat = 0 :=
    (congrArg CShape.Value.toNat
      (Store.read_applyOp_of_not_mem_storageKeys cleared (evenOrderOp cells)
        (.storage cells.zero.toCStorageRef)
        (fun member => separate.activeZero (List.mem_singleton.mp member)))).trans clearedZero
  have evenValue : (even.read (activeRead cells)).toBool =
      decide (Even (store.read (orderRead cells)).toNat) := by
    refine (congrArg CShape.Value.toBool
      (Store.read_applyOp_output cleared (evenOrderOp cells))).trans ?_
    change (Resource.BitOpcode.eval .not
      ((cleared.read (orderRead cells)).wordBitGet (Fin.last (phaseBits N)))).toBool = _
    rw [evenOrder_eval]
    exact congrArg (fun value => decide (Even value.second.toNat)) clearedExpanded
  have positiveValue : (positive.read (.storage cells.positive.toCStorageRef)).toBool =
      decide (0 < (store.read (orderRead cells)).toNat) := by
    refine (congrArg CShape.Value.toBool
      (Store.read_applyOp_output even (positiveOrderOp cells))).trans ?_
    change decide ((even.read (.storage cells.zero.toCStorageRef)).toNat <
      (even.read (orderRead cells)).toNat) = _
    rw [evenZero]
    exact congrArg (fun value => decide (0 < value.second.toNat)) evenExpanded
  have activeSame : (positive.read (activeRead cells)).toBool =
      decide (Even (store.read (orderRead cells)).toNat) :=
    (congrArg CShape.Value.toBool
      (Store.read_applyOp_of_not_mem_storageKeys even (positiveOrderOp cells) (activeRead cells)
        (fun member => separate.positiveActive (List.mem_singleton.mp member)))).trans evenValue
  have combinedValue : (combined.read (activeRead cells)).toBool =
      (decide (Even (store.read (orderRead cells)).toNat) &&
        decide (0 < (store.read (orderRead cells)).toNat)) := by
    refine (congrArg CShape.Value.toBool
      (Store.read_applyOp_output positive (positiveEvenOp cells))).trans ?_
    change (Resource.BitOpcode.eval .and (.product (positive.read (activeRead cells))
      (positive.read (.storage cells.positive.toCStorageRef)))).toBool = _
    rw [and_toBool, activeSame, positiveValue]
  refine (congrArg CShape.Value.toBool
    (Store.read_applyOp_output combined (acceptedOrderOp cells))).trans ?_
  change (Resource.BitOpcode.eval .and (.product (combined.read (activeRead cells))
    (combined.read (expandedRead cells)).first)).toBool = _
  rw [and_toBool, combinedValue, combinedExpanded]

/-- A true stored guard means exactly original acceptance and a positive even recovered order. -/
theorem guard_accepts (cells : Cells ctx N) (store : Store ctx)
    (separate : GuardSeparation cells) :
    ((guardStore cells store).read (activeRead cells)).toBool = true ↔
      (store.read (expandedRead cells)).first.toBool = true ∧
        0 < (store.read (orderRead cells)).toNat ∧
          Even (store.read (orderRead cells)).toNat := by
  rw [guard_result cells store separate]
  simp [and_comm]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
