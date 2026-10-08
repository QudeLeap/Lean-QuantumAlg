/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Word
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Correctness
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Write
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Actual complete-store semantics of raw field subtraction

The first loaded modulus and the original widened arithmetic produce the
same finite word as the closed instruction expressions. The second real
modulus load and reduction are retained. Lexical allocation supplies every
internal separation fact; the original canonical domain is needed only for
the final interpretation as nonnegative modular subtraction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual first modulus loading follows both original widened operand writes. -/
def subtractionLoadedStore (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (store : Store ctx) : Store ctx :=
  (ConstantWord.foldStep (model := model) scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
    ((store.applyOp (subtractionLeftOp left scratch)).applyOp
      (subtractionRightOp right scratch))).1

/-- The original five-stage prefix ends with the actual flagged difference. -/
def subtractionStore (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (store : Store ctx) : Store ctx :=
  ((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
    (subtractionAugmentOp scratch)).applyOp (subtractionDifferenceOp scratch)

/-- The actual finite sequence returns precisely the original chronological store. -/
theorem subtractionStageRecord_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (store : Store ctx) :
    (Circuit.forRangeStoreRecord 5
      (subtractionStage (model := model) spec left right scratch)
      (subtractionStageRecord spec left right scratch) store).1 =
      subtractionStore (model := model) spec left right scratch store := rfl

/-- Actual written identities of the five original arithmetic cells. -/
def SubScratch.keys (scratch : SubScratch ctx width) : List StorageKey :=
  [scratch.left.key, scratch.right.key, scratch.modulus.key,
    scratch.augmented.key, scratch.difference.key]

/-- Only the internally allocated arithmetic cells need separation. -/
structure SubScratch.Separation (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) : Prop where
  distinct : scratch.keys.Nodup
  left : ∀ key ∈ scratch.keys, key ∉ left.storageKeys
  right : ∀ key ∈ scratch.keys, key ∉ right.storageKeys

omit [BitWord.Selected model] in
private theorem subtraction_scratch_inequalities
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (separate : scratch.Separation left right) :
    scratch.left.key ≠ scratch.right.key ∧ scratch.modulus.key ≠ scratch.left.key ∧
      scratch.modulus.key ≠ scratch.right.key ∧ scratch.augmented.key ≠ scratch.right.key := by
  have distinct :
      (scratch.left.key ≠ scratch.right.key ∧ scratch.left.key ≠ scratch.modulus.key ∧
        scratch.left.key ≠ scratch.augmented.key ∧ scratch.left.key ≠ scratch.difference.key) ∧
      (scratch.right.key ≠ scratch.modulus.key ∧ scratch.right.key ≠ scratch.augmented.key ∧
        scratch.right.key ≠ scratch.difference.key) ∧
      (scratch.modulus.key ≠ scratch.augmented.key ∧
        scratch.modulus.key ≠ scratch.difference.key) ∧
      scratch.augmented.key ≠ scratch.difference.key := by
    simpa [SubScratch.keys] using separate.distinct
  exact ⟨distinct.1.1, Ne.symm distinct.1.2.1,
    Ne.symm distinct.2.1.1, Ne.symm distinct.2.1.2.1⟩

omit [BitWord.Selected model] in
private theorem subtraction_word_eq (first second : CShape.Word width)
    (same : first.toNat = second.toNat) : first = second := by
  cases first with
  | unsignedWord first =>
    cases second with
    | unsignedWord second => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

omit [BitWord.Selected model] in
private theorem read_product (store : Store ctx) {first second : CShape}
    (left : CInputRef ctx first) (right : CInputRef ctx second) :
    store.read (.product left right) = .product (store.read left) (store.read right) := rfl

/-- Actual first loading preserves both complete snapshots and produces the original modulus. -/
theorem subtractionLoadedStore_values (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (separate : scratch.Separation left right) (store : Store ctx) :
    (subtractionLoadedStore (model := model) spec left right scratch store).read
      (reductionRead scratch.left) =
      CShape.wordResize (width + 1) (store.read left) ∧
    (subtractionLoadedStore (model := model) spec left right scratch store).read
      (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) ∧
    (subtractionLoadedStore (model := model) spec left right scratch store).read
      (reductionRead scratch.modulus) =
      subtractionModulusWord spec := by
  obtain ⟨leftRight, modulusLeft, modulusRight, _⟩ :=
    subtraction_scratch_inequalities left right scratch separate
  have leftWritten : (store.applyOp (subtractionLeftOp left scratch)).read
      (reductionRead scratch.left) = CShape.wordResize (width + 1) (store.read left) :=
    Store.read_applyOp_output store (subtractionLeftOp left scratch)
  have rightWritten : ((store.applyOp (subtractionLeftOp left scratch)).applyOp
      (subtractionRightOp right scratch)).read (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) := by
    change ((store.applyOp (subtractionLeftOp left scratch)).applyOp
      (subtractionRightOp right scratch)).read
        (.storage (subtractionRightOp right scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.wordResize (width + 1)
      ((store.applyOp (subtractionLeftOp left scratch)).read right) = _
    rw [Store.read_applyOp_of_not_mem_storageKeys store (subtractionLeftOp left scratch)
      right (separate.right scratch.left.key (by simp [SubScratch.keys]))]
  have leftRetained : ((store.applyOp (subtractionLeftOp left scratch)).applyOp
      (subtractionRightOp right scratch)).read (reductionRead scratch.left) =
      CShape.wordResize (width + 1) (store.read left) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys _ (subtractionRightOp right scratch)
      (reductionRead scratch.left) ?_).trans leftWritten
    change scratch.right.key ∉ (reductionRead scratch.left).storageKeys
    simpa [reductionRead, CInputRef.storageKeys] using Ne.symm leftRight
  constructor
  · refine (ConstantWord.constantWord_fold_read_other (model := model) scratch.modulus _
      (reductionRead scratch.left) ?_ _).trans leftRetained
    simpa [reductionRead, CInputRef.storageKeys] using modulusLeft
  constructor
  · refine (ConstantWord.constantWord_fold_read_other (model := model) scratch.modulus _
      (reductionRead scratch.right) ?_ _).trans rightWritten
    simpa [reductionRead, CInputRef.storageKeys] using modulusRight
  · apply subtraction_word_eq
    refine (ConstantWord.constantWord_read (model := model)
      scratch.modulus spec.modulus _).trans ?_
    exact (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec)).trans
      (subtractionModulusWord_toNat spec).symm

/-- Both actual flagged arithmetic instructions give exactly their closed finite-word expression. -/
theorem subtractionStore_difference (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (separate : scratch.Separation left right) (store : Store ctx) :
    (subtractionStore (model := model) spec left right scratch store).read
      (.first (reductionRead scratch.difference)) =
        subtractionDifferenceWord spec (store.read left) (store.read right) := by
  obtain ⟨leftValue, rightValue, modulusValue⟩ :=
    subtractionLoadedStore_values spec left right scratch separate store
  have augmented : ((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
      (subtractionAugmentOp scratch)).read (reductionRead scratch.augmented) =
      CShape.addCarry (width + 1) (.product (CShape.wordResize (width + 1) (store.read left))
        (subtractionModulusWord spec)) := by
    change ((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
      (subtractionAugmentOp scratch)).read
        (.storage (subtractionAugmentOp scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.addCarry (width + 1)
      ((subtractionLoadedStore (model := model) spec left right scratch store).read
        (.product (reductionRead scratch.left) (reductionRead scratch.modulus))) = _
    rw [read_product, leftValue, modulusValue]
  have retainedRight :
      ((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
        (subtractionAugmentOp scratch)).read (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys _ (subtractionAugmentOp scratch)
      (reductionRead scratch.right) ?_).trans rightValue
    change scratch.augmented.key ∉ (reductionRead scratch.right).storageKeys
    simpa [reductionRead, CInputRef.storageKeys] using
      (subtraction_scratch_inequalities left right scratch separate).2.2.2
  have difference : (subtractionStore (model := model) spec left right scratch store).read
      (reductionRead scratch.difference) = CShape.subBorrow (width + 1)
        (.product (subtractionAugmentedWord spec (store.read left))
          (CShape.wordResize (width + 1) (store.read right))) := by
    change (((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
      (subtractionAugmentOp scratch)).applyOp (subtractionDifferenceOp scratch)).read
        (.storage (subtractionDifferenceOp scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.subBorrow (width + 1) ((Store.applyOp
      (subtractionLoadedStore (model := model) spec left right scratch store)
        (subtractionAugmentOp scratch)).read
        (.product (.first (reductionRead scratch.augmented)) (reductionRead scratch.right))) = _
    rw [read_product, retainedRight]
    change CShape.subBorrow (width + 1) (.product
      (((subtractionLoadedStore (model := model) spec left right scratch store).applyOp
        (subtractionAugmentOp scratch)).read (reductionRead scratch.augmented)).first _) = _
    rw [augmented]
    rfl
  exact congrArg CShape.Value.first difference

private theorem subtractionStore_preserves (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (store : Store ctx) {shape : CShape} (input : CInputRef ctx shape)
    (separate : ∀ key ∈ scratch.keys, key ∉ input.storageKeys) :
    (subtractionStore (model := model) spec left right scratch store).read input =
      store.read input := by
  have leftFree := separate scratch.left.key (by simp [SubScratch.keys])
  have rightFree := separate scratch.right.key (by simp [SubScratch.keys])
  have modulusFree := separate scratch.modulus.key (by simp [SubScratch.keys])
  have augmentedFree := separate scratch.augmented.key (by simp [SubScratch.keys])
  have differenceFree := separate scratch.difference.key (by simp [SubScratch.keys])
  unfold subtractionStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (subtractionDifferenceOp scratch) input
    differenceFree, Store.read_applyOp_of_not_mem_storageKeys _ (subtractionAugmentOp scratch)
      input augmentedFree]
  unfold subtractionLoadedStore
  rw [ConstantWord.constantWord_fold_read_other (model := model)
      scratch.modulus _ input modulusFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (subtractionRightOp right scratch) input rightFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (subtractionLeftOp left scratch) input leftFree]

/-- On every raw input the actual body returns the same finite native subtraction word. -/
theorem subtractionBody_word (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (separate : scratch.Separation left right) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (subtractionBodyStep spec left right scratch output store).1.read (reductionRead output) =
      subtractionWord spec (store.read left) (store.read right) := by
  apply subtraction_word_eq
  change ((reduceIntoWordStep spec (.first (reductionRead scratch.difference)) output
    (subtractionStore (model := model) spec left right scratch store)).1.read
      (reductionRead output)).toNat = _
  rw [reduceIntoWord_toNat, subtractionStore_difference spec left right scratch separate store]
  have modulusValue := subtractionModulusWord_toNat spec
  have result := reductionValue_toNat
    (subtractionDifferenceWord spec (store.read left) (store.read right))
    (subtractionModulusWord spec) (modulusValue ▸ modulusSpec_modulus_pos spec)
    (modulusValue ▸ spec.le_capacity)
  rw [modulusValue] at result
  exact result.symm

/-- The actual body changes precisely its caller output after the five scratch updates. -/
theorem subtractionBody_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (separate : scratch.Separation left right) (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (subtractionBodyStep spec left right scratch output store).1 =
      (subtractionStore (model := model) spec left right scratch store).write output
        (subtractionWord spec (store.read left) (store.read right)) := by
  apply Store.store_eq_write_of_read_frame
  · exact subtractionBody_word spec left right scratch separate output store
  · intro otherShape other free
    change (reduceIntoWordStep spec _ output
      (subtractionStore (model := model) spec left right scratch store)).1.read (.storage other) = _
    apply reduceIntoWord_read_other
    simpa [CInputRef.storageKeys] using free

omit [BitWord.Selected model] in
private theorem subtractionScratch_keys (cells : Cells ctx (subtractionShapes width)) :
    (subtractionScratch cells).keys = cells.keys.reverse := by
  cases cells with
  | cons difference rest =>
    cases rest with
    | cons augmented rest =>
      cases rest with
      | cons modulus rest =>
        cases rest with
        | cons right rest =>
          cases rest with
          | cons left rest =>
            cases rest
            rfl

omit [BitWord.Selected model] in
private theorem subtractionScratch_separation {outer : RuntimeCtx model.kind}
    (left right : CInputRef outer (.unsignedWord width))
    (cells : Cells ctx (subtractionShapes width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport) :
    (subtractionScratch cells).Separation (transport.liftInput left)
      (transport.liftInput right) := by
  constructor
  · rw [subtractionScratch_keys]
    simpa only [List.nodup_reverse] using Cells.workspaceCells_distinct_keys_nodup cells distinct
  · intro key member
    rw [subtractionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) left
  · intro key member
    rw [subtractionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) right

/-- Actual allocation supplies every scratch condition and returns the exact finite native word. -/
theorem subIntoWord_actualRecord (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ∃ step : Store ctx → Store ctx ×
      (subIntoWord (model := model) spec left right output).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (subIntoWord (model := model) spec left right output).execute Reference state =
          state.mapClassical (fun entry => ((step entry.1).1,
            (entry.2.1, (entry.2.2, (step entry.1).2))))) ∧
      ∀ before : Store ctx, (step before).1 = before.write output
        (subtractionWord spec (before.read left) (before.read right)) := by
  apply withCells_actualStoreRecord_post ctx (subtractionShapes width)
    (fun cells _ transport _ => subtractionBody spec (transport.liftInput left)
      (transport.liftInput right) (subtractionScratch cells) (transport.liftWrite output))
    (fun source target => target = source.write output
      (subtractionWord spec (source.read left) (source.read right)))
  intro inner cells distinct transport separated
  refine ⟨subtractionBodyStep spec (transport.liftInput left) (transport.liftInput right)
    (subtractionScratch cells) (transport.liftWrite output), subtractionBody_execute _ _ _ _ _, ?_⟩
  intro source before reads
  let value := subtractionWord spec (source.read left) (source.read right)
  refine ⟨source.write output value, rfl, ?_⟩
  have bodyResult := subtractionBody_store spec
    (transport.liftInput left) (transport.liftInput right)
    (subtractionScratch cells)
    (subtractionScratch_separation left right cells distinct transport separated)
    (transport.liftWrite output) before
  have valueSame : subtractionWord spec (before.read (transport.liftInput left))
      (before.read (transport.liftInput right)) = value := by
    rw [reads left, reads right]
  have scratchReads : transport.ReadsAs source
      (subtractionStore (model := model) spec (transport.liftInput left)
        (transport.liftInput right) (subtractionScratch cells) before) := by
    intro shape input
    refine (subtractionStore_preserves _ _ _ _ _ (transport.liftInput input) ?_).trans (reads input)
    intro key member
    rw [subtractionScratch_keys] at member
    exact Cells.workspaceCells_transportSeparated_avoids_of_mem cells transport separated
      (List.mem_reverse.mp member) input
  rw [valueSame] at bodyResult
  apply (congrArg (transport.ReadsAs (source.write output value)) bodyResult).mpr
  intro shape input
  exact transport.workspaceTransport_readsAs_write scratchReads output value input

/-- This record is certified by all original instructions and actual lexical releases. -/
def subIntoWordStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (subIntoWord (model := model) spec left right output).Path :=
  Classical.choose (subIntoWord_actualRecord spec left right output)

/-- Both original modulus loads preserve complete reference correlations and execution history. -/
theorem subIntoWord_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (subIntoWord (model := model) spec left right output).execute Reference state =
      state.mapClassical
      (fun entry => ((subIntoWordStep spec left right output entry.1).1,
        (entry.2.1, (entry.2.2, (subIntoWordStep spec left right output entry.1).2)))) :=
  (Classical.choose_spec (subIntoWord_actualRecord spec left right output)).1 Reference state

/-- The actual finite native value overwrites exactly the chosen caller result cell. -/
theorem subIntoWordStep_store (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (subIntoWordStep spec left right output store).1 = store.write output
      (subtractionWord spec (store.read left) (store.read right)) :=
  (Classical.choose_spec (subIntoWord_actualRecord spec left right output)).2 store

/-- The original canonical operand domain gives exact modular subtraction in the destination. -/
theorem subIntoWord_toNat (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (rightCanonical : (store.read right).toNat < spec.modulus) :
    ((subIntoWordStep spec left right output store).1.read (reductionRead output)).toNat =
      ((store.read left).toNat + spec.modulus - (store.read right).toNat) % spec.modulus := by
  rw [subIntoWordStep_store]
  change ((store.write output (subtractionWord spec (store.read left) (store.read right))).read
    (.storage output.toCStorageRef)).toNat = _
  rw [Store.read_write_same]
  exact subtractionWord_toNat spec (store.read left) (store.read right) rightCanonical

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
