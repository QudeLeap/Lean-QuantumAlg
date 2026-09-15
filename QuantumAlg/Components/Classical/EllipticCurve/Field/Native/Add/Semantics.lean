/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Exact actual raw field-addition semantics

Widening preserves every operand bit, and the widened sum cannot overflow.
The original loaded reduction gives the exact modular sum. Fresh allocation
discharges all internal separation conditions, including arbitrary caller
input aliases and any previous contents of the actual result cell.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original three actual arithmetic updates, before entering loaded reduction. -/
def additionStore (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (additionLeftOp left scratch)).applyOp
    (additionRightOp right scratch)).applyOp (additionSumOp scratch)

/-- The actual finite arithmetic record returns exactly those three chronological updates. -/
theorem additionStageRecord_store (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (store : Store ctx) :
    (Circuit.forRangeRecord 3 (additionStage left right scratch)
      (additionStageRecord left right scratch) store).1 =
      additionStore left right scratch store := rfl

/-- Actual storage identities written by the original arithmetic prefix. -/
def AddScratch.keys (scratch : AddScratch ctx width) : List StorageKey :=
  [scratch.left.key, scratch.right.key, scratch.sum.key]

/-- Only internal scratch cells need separation from each other and the raw operands. -/
structure AddScratch.Separation (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  left : ∀ key ∈ scratch.keys, key ∉ left.storageKeys
  right : ∀ key ∈ scratch.keys, key ∉ right.storageKeys

private theorem widened_toNat (value : CShape.Word width) :
    (CShape.wordResize (width + 1) value).toNat = value.toNat := by
  change value.toNat % 2 ^ (width + 1) = _
  apply Nat.mod_eq_of_lt
  have bound := value.toNat_lt
  rw [pow_succ]
  omega

private theorem widened_add_toNat (left right : CShape.Word width) :
    (CShape.addCarry (width + 1)
      (.product (CShape.wordResize (width + 1) left)
        (CShape.wordResize (width + 1) right))).first.toNat = left.toNat + right.toNat := by
  change ((CShape.wordResize (width + 1) left).toNat +
    (CShape.wordResize (width + 1) right).toNat) % 2 ^ (width + 1) = _
  rw [widened_toNat, widened_toNat]
  apply Nat.mod_eq_of_lt
  have leftBound := left.toNat_lt
  have rightBound := right.toNat_lt
  rw [pow_succ]
  omega

private theorem read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

/-- The actual widened sum is the exact natural sum of both original raw operands. -/
theorem additionStore_sum (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (separate : scratch.Separation left right)
    (store : Store ctx) :
    ((additionStore left right scratch store).read (.first (reductionRead scratch.sum))).toNat =
      (store.read left).toNat + (store.read right).toNat := by
  have different : scratch.left.key ≠ scratch.right.key := by
    have noLeft : scratch.left.key ∉ [scratch.right.key, scratch.sum.key] :=
      (List.nodup_cons.mp separate.distinct).1
    exact fun same => noLeft (by simp [same])
  have leftWritten : (store.applyOp (additionLeftOp left scratch)).read
      (reductionRead scratch.left) = CShape.wordResize (width + 1) (store.read left) :=
    Store.read_applyOp_output store (additionLeftOp left scratch)
  have rightWritten : ((store.applyOp (additionLeftOp left scratch)).applyOp
      (additionRightOp right scratch)).read (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) := by
    change ((store.applyOp (additionLeftOp left scratch)).applyOp
      (additionRightOp right scratch)).read
        (.storage (additionRightOp right scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.wordResize (width + 1)
      ((store.applyOp (additionLeftOp left scratch)).read right) = _
    rw [Store.read_applyOp_of_not_mem_storageKeys store (additionLeftOp left scratch)
      right (separate.right scratch.left.key (by simp [AddScratch.keys]))]
  have leftRetained : ((store.applyOp (additionLeftOp left scratch)).applyOp
      (additionRightOp right scratch)).read (reductionRead scratch.left) =
      CShape.wordResize (width + 1) (store.read left) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys _ (additionRightOp right scratch)
      (reductionRead scratch.left) ?_).trans leftWritten
    change scratch.right.key ∉ (reductionRead scratch.left).storageKeys
    simpa [reductionRead, CInputRef.storageKeys] using Ne.symm different
  have sumWritten : (additionStore left right scratch store).read (reductionRead scratch.sum) =
      CShape.addCarry (width + 1)
        (.product (CShape.wordResize (width + 1) (store.read left))
          (CShape.wordResize (width + 1) (store.read right))) := by
    change (((store.applyOp (additionLeftOp left scratch)).applyOp
      (additionRightOp right scratch)).applyOp (additionSumOp scratch)).read
        (.storage (additionSumOp scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.addCarry (width + 1)
      (((store.applyOp (additionLeftOp left scratch)).applyOp
        (additionRightOp right scratch)).read
          (.product (reductionRead scratch.left) (reductionRead scratch.right))) = _
    rw [read_product, leftRetained, rightWritten]
  change ((additionStore left right scratch store).read (reductionRead scratch.sum)).first.toNat = _
  rw [sumWritten]
  exact widened_add_toNat _ _

private theorem additionStore_preserves (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (additionStore left right scratch store).read input = store.read input := by
  have leftFree := separate scratch.left.key (by simp [AddScratch.keys])
  have rightFree := separate scratch.right.key (by simp [AddScratch.keys])
  have sumFree := separate scratch.sum.key (by simp [AddScratch.keys])
  unfold additionStore
  repeat rw [Store.read_applyOp_of_not_mem_storageKeys]
  all_goals first | rfl | exact leftFree | exact rightFree | exact sumFree

private theorem word_eq_of_toNat (first second : CShape.Word width)
    (same : first.toNat = second.toNat) : first = second := by
  cases first with
  | unsignedWord first =>
    cases second with
    | unsignedWord second => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- Exact modular arithmetic is computed by the actual addition and loaded-reduction body. -/
theorem additionBody_toNat (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (separate : scratch.Separation left right) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    ((additionBodyStep spec left right scratch output store).1.read (reductionRead output)).toNat =
      ((store.read left).toNat + (store.read right).toNat) % spec.modulus := by
  change ((reduceIntoWordStep spec (.first (reductionRead scratch.sum)) output
    (additionStore left right scratch store)).1.read (reductionRead output)).toNat = _
  rw [reduceIntoWord_toNat, additionStore_sum left right scratch separate store]

/-- The actual loaded reduction changes only its result after the arithmetic scratch updates. -/
theorem additionBody_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (separate : scratch.Separation left right) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (additionBodyStep spec left right scratch output store).1 =
      (additionStore left right scratch store).write output
        (CShape.wordOfNat width (((store.read left).toNat + (store.read right).toNat) %
          spec.modulus)) := by
  apply Store.store_eq_write_of_read_frame
  · apply word_eq_of_toNat
    refine (additionBody_toNat spec left right scratch separate output store).trans ?_
    change _ = (_ % spec.modulus) % 2 ^ width
    exact (Nat.mod_eq_of_lt (lt_of_lt_of_le
      (Nat.mod_lt _ (modulusSpec_modulus_pos spec)) spec.le_capacity)).symm
  · intro otherShape other free
    change (reduceIntoWordStep spec _ output (additionStore left right scratch store)).1.read
      (.storage other) = _
    apply reduceIntoWord_read_other
    simpa [CInputRef.storageKeys] using free

private theorem additionScratch_keys (cells : Cells ctx (additionShapes width)) :
    (additionScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons sum rest =>
    cases rest with
    | cons right rest =>
      cases rest with
      | cons left rest =>
        cases rest
        rfl

private theorem additionScratch_separation {outer : RuntimeCtx kind}
    (left right : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (additionShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (additionScratch cells).Separation (transport.liftInput left) (transport.liftInput right) := by
  constructor
  · rw [additionScratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [additionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) left
  · intro key member
    rw [additionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) right

/-- Actual allocation gives the exact caller-store sum without external workspace promises. -/
theorem addIntoWord_actualRecord (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ step : Store ctx → Store ctx × (addIntoWord spec left right output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (addIntoWord spec left right output).execute Reference state = state.mapClassical
          (fun entry => ((step entry.1).1, (entry.2, (step entry.1).2)))) ∧
      ∀ before : Store ctx, (step before).1 = before.write output
        (CShape.wordOfNat width (((before.read left).toNat + (before.read right).toNat) %
          spec.modulus)) := by
  apply withCells_actualRecord_post ctx (additionShapes width)
    (fun cells _ transport _ => additionBody spec (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) (transport.liftWrite output))
    (fun source target => target = source.write output
      (CShape.wordOfNat width
        (((source.read left).toNat + (source.read right).toNat) % spec.modulus)))
  intro inner cells distinct transport separated
  refine ⟨additionBodyStep spec (transport.liftInput left) (transport.liftInput right)
    (additionScratch cells) (transport.liftWrite output), additionBody_execute _ _ _ _ _, ?_⟩
  intro source before reads
  let value := CShape.wordOfNat width
    (((source.read left).toNat + (source.read right).toNat) % spec.modulus)
  refine ⟨source.write output value, rfl, ?_⟩
  have bodyResult := additionBody_store spec (transport.liftInput left) (transport.liftInput right)
    (additionScratch cells)
    (additionScratch_separation left right cells distinct transport separated)
    (transport.liftWrite output) before
  have valueSame : CShape.wordOfNat width
      (((before.read (transport.liftInput left)).toNat +
        (before.read (transport.liftInput right)).toNat) % spec.modulus) = value := by
    rw [reads left, reads right]
  have scratchReads : transport.ReadsAs source (additionStore (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) before) := by
    intro shape input
    refine (additionStore_preserves _ _ _ _ (transport.liftInput input) ?_).trans (reads input)
    intro key member
    rw [additionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) input
  rw [valueSame] at bodyResult
  apply (congrArg (transport.ReadsAs (source.write output value)) bodyResult).mpr
  intro shape input
  exact transport.workspaceTransport_readsAs_write scratchReads output value input

/-- This record is certified by actual allocation, arithmetic, reduction and release. -/
def addIntoWordStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (addIntoWord spec left right output).Path :=
  Classical.choose (addIntoWord_actualRecord spec left right output)

/-- The complete actual addition retains arbitrary quantum-reference correlations and history. -/
theorem addIntoWord_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (addIntoWord spec left right output).execute Reference state = state.mapClassical
      (fun entry => ((addIntoWordStep spec left right output entry.1).1,
        (entry.2, (addIntoWordStep spec left right output entry.1).2))) :=
  (Classical.choose_spec (addIntoWord_actualRecord spec left right output)).1 Reference state

/-- Exactly the caller's chosen result is overwritten with the canonical modular sum. -/
theorem addIntoWordStep_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (addIntoWordStep spec left right output store).1 = store.write output
      (CShape.wordOfNat width
        (((store.read left).toNat + (store.read right).toNat) % spec.modulus)) :=
  (Classical.choose_spec (addIntoWord_actualRecord spec left right output)).2 store

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
