/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add.Semantics

/-!
# Exact Store semantics of addition using an existing modulus

All three caller inputs are read before the result write. The output may
alias either operand. The fresh internal arithmetic cells preserve the
stored modulus and every other caller cell, including table arrays.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Total finite-word result of the five actual native instructions. -/
def addValue (left right : CShape.Word width) (modulus : CShape.Word (width + 1)) :
    CShape.Word width :=
  reductionValue (CShape.wordOfNat (width + 1) (left.toNat + right.toNat)) modulus

private lemma word_ext {n : Nat} (first second : CShape.Word n)
    (same : first.toNat = second.toNat) : first = second := by
  cases first with
  | unsignedWord first =>
    cases second with
    | unsignedWord second => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

private lemma sum_fits (left right : CShape.Word width) :
    left.toNat + right.toNat < 2 ^ (width + 1) := by
  have leftBound := left.toNat_lt
  have rightBound := right.toNat_lt
  rw [pow_succ]
  omega

/-- A fitted positive stored modulus gives the canonical modular sum. -/
lemma addValue_toNat (left right : CShape.Word width) (modulus : CShape.Word (width + 1))
    (positive : 0 < modulus.toNat) (fits : modulus.toNat ≤ 2 ^ width) :
    (addValue left right modulus).toNat = (left.toNat + right.toNat) % modulus.toNat := by
  rw [addValue, reductionValue_toNat _ _ positive fits]
  change ((left.toNat + right.toNat) % 2 ^ (width + 1)) % modulus.toNat = _
  rw [Nat.mod_eq_of_lt (sum_fits left right)]

private lemma arithmetic_preserves (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape) (separate : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (additionStore left right scratch store).read input = store.read input := by
  have leftFree := separate scratch.left.key (by simp [AddScratch.keys])
  have rightFree := separate scratch.right.key (by simp [AddScratch.keys])
  have sumFree := separate scratch.sum.key (by simp [AddScratch.keys])
  unfold additionStore
  repeat rw [Store.read_applyOp_of_not_mem_storageKeys]
  all_goals first | rfl | exact leftFree | exact rightFree | exact sumFree

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual five-operation body returns the finite value of the original three inputs. -/
lemma addBody_value (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (separate : scratch.Separation left right)
    (modulusFree : ∀ key ∈ scratch.keys, key ∉ modulus.storageKeys)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (addBodyStep (model := model) left right modulus scratch output store).1.read
      (reductionRead output) = addValue (store.read left) (store.read right) (store.read modulus) :=
    by
  change (reduceWordStep (.first (reductionRead scratch.sum)) modulus output
    (additionStore left right scratch store)).1.read (reductionRead output) = _
  rw [reduceWord_value, arithmetic_preserves left right scratch store modulus modulusFree]
  have sumValue : (additionStore left right scratch store).read
      (.first (reductionRead scratch.sum)) =
      CShape.wordOfNat (width + 1) ((store.read left).toNat + (store.read right).toNat) := by
    apply word_ext
    refine (additionStore_sum left right scratch separate store).trans ?_
    exact (Nat.mod_eq_of_lt (sum_fits (store.read left) (store.read right))).symm
  rw [sumValue]
  rfl

/-- Only the result changes after the actual reduction; arithmetic scratch is kept explicit. -/
lemma addBody_store (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (separate : scratch.Separation left right)
    (modulusFree : ∀ key ∈ scratch.keys, key ∉ modulus.storageKeys)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (addBodyStep (model := model) left right modulus scratch output store).1 =
      (additionStore left right scratch store).write output
        (addValue (store.read left) (store.read right) (store.read modulus)) := by
  apply Store.store_eq_write_of_read_frame
  · exact addBody_value left right modulus scratch separate modulusFree output store
  · intro shape other free
    change (reduceWordStep _ modulus output (additionStore left right scratch store)).1.read
      (.storage other) = _
    apply reduceWord_read_other
    simpa [CInputRef.storageKeys] using free

omit [BitWord.Selected model] in
private lemma scratch_keys (cells : Cells ctx (additionShapes width)) :
    (additionScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons sum rest =>
    cases rest with
    | cons right rest =>
      cases rest with
      | cons left rest => cases rest; rfl

omit [BitWord.Selected model] in
private lemma scratch_separation {outer : RuntimeCtx model.kind}
    (left right : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (additionShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (additionScratch cells).Separation (transport.liftInput left) (transport.liftInput right) := by
  constructor
  · rw [scratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [scratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) left
  · intro key member
    rw [scratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) right

/-- Fresh allocation gives a complete actual record and exact one-result caller Store update. -/
lemma addIntoWord_actualRecord (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ step : Store ctx → Store ctx × (addIntoWord (model := model) left right modulus output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (addIntoWord (model := model) left right modulus output).execute environment Reference
          state = state.mapClassical (fun entry => ((step entry.1).1,
            (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
      ∀ before : Store ctx, (step before).1 = before.write output
        (addValue (before.read left) (before.read right) (before.read modulus)) := by
  apply withCells_actualStoreRecord_post (environment := environment) ctx (additionShapes width)
    (fun cells _ transport _ => addBody (transport.liftInput left) (transport.liftInput right)
      (transport.liftInput modulus) (additionScratch cells) (transport.liftWrite output))
    (fun source target => target = source.write output
      (addValue (source.read left) (source.read right) (source.read modulus)))
  intro inner cells distinct transport separated
  have free {shape : CShape} (input : CInputRef ctx shape) :
      ∀ key ∈ (additionScratch cells).keys, key ∉ (transport.liftInput input).storageKeys := by
    intro key member
    rw [scratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) input
  refine ⟨addBodyStep (transport.liftInput left) (transport.liftInput right)
    (transport.liftInput modulus) (additionScratch cells) (transport.liftWrite output),
    addBody_execute _ _ _ _ _, ?_⟩
  intro source before reads
  let value := addValue (source.read left) (source.read right) (source.read modulus)
  refine ⟨source.write output value, rfl, ?_⟩
  have result := addBody_store (transport.liftInput left) (transport.liftInput right)
    (transport.liftInput modulus) (additionScratch cells)
    (scratch_separation left right cells distinct transport separated) (free modulus)
    (transport.liftWrite output) before
  have valueSame : addValue (before.read (transport.liftInput left))
      (before.read (transport.liftInput right)) (before.read (transport.liftInput modulus)) =
      value := by rw [reads left, reads right, reads modulus]
  have scratchReads : transport.ReadsAs source (additionStore (transport.liftInput left)
      (transport.liftInput right) (additionScratch cells) before) := by
    intro shape input
    exact (arithmetic_preserves _ _ _ _ (transport.liftInput input) (free input)).trans
      (reads input)
  rw [valueSame] at result
  apply (congrArg (transport.ReadsAs (source.write output value)) result).mpr
  intro shape input
  exact transport.workspaceTransport_readsAs_write scratchReads output value input

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
