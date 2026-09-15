/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Branches
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Guard.Correctness
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Encoding
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Mathematics

/-!
# Actual accepted-order reduction agrees with the source selector

The real five-write guard preserves the same decoded order and base operands.
Its true arm executes the actual modular half-power and scoped GCD selector;
its false arm writes the canonical absent option through the real pack.
All separation premises here describe the internal physical cells, and the
complete enclosing workspace proves them without extra source assumptions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

private theorem guardChoice_read (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx) :
    (guardChoiceStep source cells output store).1.read (.storage output.toCStorageRef) =
      if (store.read (activeRead cells)).toBool then
        (reduceStep source cells output store).1.read (.storage output.toCStorageRef)
      else (store.applyOp (packOutputOp cells output)).read (.storage output.toCStorageRef) := by
  simp only [guardChoiceStep]
  cases store.read (activeRead cells) with
  | bit value => cases value <;> rfl

/-- Actual order checking returns precisely the source's positive-even accepted reduction. -/
theorem checked_result (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : GuardSeparation cells)
    (zeroBase : cells.zero.key ≠ cells.base.key)
    (activeBase : cells.active.key ≠ cells.base.key)
    (positiveBase : cells.positive.key ≠ cells.base.key)
    (baseValue : ClassicalAlgorithms.Modular.Residue (modulusSpec source))
    (orderValue : ClassicalAlgorithms.Word (phaseBits N + 1)) (accepted : Bool)
    (baseRead : store.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue baseValue.toWord)
    (expandedValue : store.read (expandedRead cells) =
      .product (.bit accepted) (.unsignedWord orderValue)) :
    (checkedStep source cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N)
        (if accepted = true ∧ 0 < orderValue.val ∧ Even orderValue.val then
          factorFromHalfPowerValue N (baseValue.val ^ (orderValue.val / 2) % N)
        else none) := by
  let guarded := guardStore cells store
  have originalOrder : store.read (orderRead cells) = .unsignedWord orderValue :=
    congrArg CShape.Value.second expandedValue
  have guardedExpanded : guarded.read (expandedRead cells) =
      store.read (expandedRead cells) :=
    guard_read_other cells (expandedRead cells)
      (fun member => separate.zeroExpanded (List.mem_singleton.mp member))
      (fun member => separate.activeExpanded (List.mem_singleton.mp member))
      (fun member => separate.positiveExpanded (List.mem_singleton.mp member)) store
  have guardedOrder : guarded.read (orderRead cells) = .unsignedWord orderValue :=
    (congrArg CShape.Value.second guardedExpanded).trans originalOrder
  have guardedBase : guarded.read (.storage cells.base.toCStorageRef) =
      .canonicalResidue baseValue.toWord :=
    (guard_read_other cells (.storage cells.base.toCStorageRef)
      (fun member => zeroBase (List.mem_singleton.mp member))
      (fun member => activeBase (List.mem_singleton.mp member))
      (fun member => positiveBase (List.mem_singleton.mp member)) store).trans baseRead
  have activeIff : (guarded.read (activeRead cells)).toBool = true ↔
      accepted = true ∧ 0 < orderValue.val ∧ Even orderValue.val :=
    (guard_accepts cells store separate).trans (by rw [expandedValue, originalOrder]; rfl)
  change (guardChoiceStep source cells output guarded).1.read (.storage output.toCStorageRef) = _
  rw [guardChoice_read]
  by_cases active : (guarded.read (activeRead cells)).toBool = true
  · rw [if_pos active, if_pos (activeIff.mp active)]
    exact reduce_result source cells output guarded baseValue orderValue guardedBase guardedOrder
  · rw [if_neg active, packOutput_result, if_neg active,
      if_neg (fun accepted => active (activeIff.mpr accepted))]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
