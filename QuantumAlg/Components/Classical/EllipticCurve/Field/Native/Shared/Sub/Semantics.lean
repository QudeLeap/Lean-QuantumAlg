/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub.Word
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Exact shared-modulus subtraction values

All raw input words retain their actual wrapping semantics. The canonical
right-operand condition is used only when interpreting that same finite
value as field subtraction. The modulus is an existing read-only caller
cell throughout the six paid operations.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution Modular.Reduce.Native ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Total finite-word result of widening, augmenting, subtracting and reducing. -/
def subValue (left right : CShape.Word width) (modulus : CShape.Word (width + 1)) :
    CShape.Word width :=
  reductionValue
    (CShape.subBorrow (width + 1) (.product
      (CShape.addCarry (width + 1)
        (.product (CShape.wordResize (width + 1) left) modulus)).first
      (CShape.wordResize (width + 1) right))).first modulus

private lemma word_ext {n : Nat} (first second : CShape.Word n)
    (same : first.toNat = second.toNat) : first = second := by
  cases first with
  | unsignedWord first =>
    cases second with
    | unsignedWord second => exact congrArg CShape.Value.unsignedWord (Fin.ext same)

/-- The valid canonical-right domain gives precisely modular subtraction, without a borrow. -/
lemma subValue_toNat (spec : ModulusSpec width) (left right : CShape.Word width)
    (modulus : CShape.Word (width + 1)) (modulusValue : modulus.toNat = spec.modulus)
    (rightCanonical : right.toNat < spec.modulus) :
    (subValue left right modulus).toNat =
      (left.toNat + spec.modulus - right.toNat) % spec.modulus := by
  have same : modulus = subtractionModulusWord spec := by
    apply word_ext
    exact modulusValue.trans (subtractionModulusWord_toNat spec).symm
  rw [same]
  exact subtractionWord_toNat spec left right rightCanonical

/-- Exactly the four temporary keys written by the arithmetic prefix. -/
def subWrittenKeys (scratch : SubScratch ctx width) : List StorageKey :=
  [scratch.left.key, scratch.right.key, scratch.augmented.key, scratch.difference.key]

/-- Only the fresh arithmetic scratch must avoid caller operands and the shared modulus. -/
structure SubSeparation (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) : Prop where
  distinct : (subWrittenKeys scratch).Nodup
  left : ∀ key ∈ subWrittenKeys scratch, key ∉ left.storageKeys
  right : ∀ key ∈ subWrittenKeys scratch, key ∉ right.storageKeys
  modulus : ∀ key ∈ subWrittenKeys scratch,
    key ∉ (reductionRead scratch.modulus).storageKeys

/-- The actual four chronological arithmetic writes, with no modulus materialization. -/
def subStore (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (store : Store ctx) : Store ctx :=
  (((store.applyOp (subtractionLeftOp left scratch)).applyOp
    (subtractionRightOp right scratch)).applyOp (subtractionAugmentOp scratch)).applyOp
      (subtractionDifferenceOp scratch)

/-- Caller reads outside the four actual temporary writes remain unchanged. -/
lemma subStore_preserves (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (store : Store ctx) {shape : CShape}
    (input : CInputRef ctx shape)
    (separate : ∀ key ∈ subWrittenKeys scratch, key ∉ input.storageKeys) :
    (subStore left right scratch store).read input = store.read input := by
  have leftFree := separate scratch.left.key (by simp [subWrittenKeys])
  have rightFree := separate scratch.right.key (by simp [subWrittenKeys])
  have augmentedFree := separate scratch.augmented.key (by simp [subWrittenKeys])
  have differenceFree := separate scratch.difference.key (by simp [subWrittenKeys])
  unfold subStore
  repeat rw [Store.read_applyOp_of_not_mem_storageKeys]
  all_goals first
    | rfl | exact leftFree | exact rightFree | exact augmentedFree | exact differenceFree

/-- The stored difference is exactly the finite arithmetic expression on the original inputs. -/
lemma subStore_difference (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (separate : SubSeparation left right scratch)
    (store : Store ctx) :
    (subStore left right scratch store).read (.first (reductionRead scratch.difference)) =
      (CShape.subBorrow (width + 1) (.product
        (CShape.addCarry (width + 1) (.product
          (CShape.wordResize (width + 1) (store.read left))
          (store.read (reductionRead scratch.modulus)))).first
        (CShape.wordResize (width + 1) (store.read right)))).first := by
  have leftRight : scratch.left.key ≠ scratch.right.key := by
    have absent := (List.nodup_cons.mp separate.distinct).1
    exact fun same => absent (by simp [same])
  have rightAugmented : scratch.right.key ≠ scratch.augmented.key := by
    have absent := (List.nodup_cons.mp (List.nodup_cons.mp separate.distinct).2).1
    exact fun same => absent (by simp [same])
  let first := store.applyOp (subtractionLeftOp left scratch)
  let second := first.applyOp (subtractionRightOp right scratch)
  let third := second.applyOp (subtractionAugmentOp scratch)
  have leftWritten : first.read (reductionRead scratch.left) =
      CShape.wordResize (width + 1) (store.read left) :=
    Store.read_applyOp_output store (subtractionLeftOp left scratch)
  have rightWritten : second.read (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) := by
    change (first.applyOp (subtractionRightOp right scratch)).read
      (.storage (subtractionRightOp right scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.wordResize (width + 1) (first.read right) = _
    rw [Store.read_applyOp_of_not_mem_storageKeys store (subtractionLeftOp left scratch)
      right (separate.right scratch.left.key (by simp [subWrittenKeys]))]
  have leftRetained : second.read (reductionRead scratch.left) =
      CShape.wordResize (width + 1) (store.read left) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys first (subtractionRightOp right scratch)
      (reductionRead scratch.left) ?_).trans leftWritten
    change scratch.right.key ∉ (reductionRead scratch.left).storageKeys
    simpa [reductionRead, CInputRef.storageKeys] using Ne.symm leftRight
  have modulusRetained : second.read (reductionRead scratch.modulus) =
      store.read (reductionRead scratch.modulus) := by
    change (first.applyOp (subtractionRightOp right scratch)).read _ = _
    rw [Store.read_applyOp_of_not_mem_storageKeys first (subtractionRightOp right scratch)
      (reductionRead scratch.modulus)
      (separate.modulus scratch.right.key (by simp [subWrittenKeys])),
      Store.read_applyOp_of_not_mem_storageKeys store (subtractionLeftOp left scratch)
        (reductionRead scratch.modulus)
        (separate.modulus scratch.left.key (by simp [subWrittenKeys]))]
  have augmented : third.read (reductionRead scratch.augmented) =
      CShape.addCarry (width + 1) (.product
        (CShape.wordResize (width + 1) (store.read left))
        (store.read (reductionRead scratch.modulus))) := by
    change (second.applyOp (subtractionAugmentOp scratch)).read
      (.storage (subtractionAugmentOp scratch).outputRef.toCStorageRef) = _
    rw [Store.read_applyOp_output]
    change CShape.addCarry (width + 1) (.product
      (second.read (reductionRead scratch.left))
      (second.read (reductionRead scratch.modulus))) = _
    rw [leftRetained, modulusRetained]
  have rightRetained : third.read (reductionRead scratch.right) =
      CShape.wordResize (width + 1) (store.read right) := by
    refine (Store.read_applyOp_of_not_mem_storageKeys second (subtractionAugmentOp scratch)
      (reductionRead scratch.right) ?_).trans rightWritten
    change scratch.augmented.key ∉ (reductionRead scratch.right).storageKeys
    simpa [reductionRead, CInputRef.storageKeys] using Ne.symm rightAugmented
  have difference := Store.read_applyOp_output third (subtractionDifferenceOp scratch)
  change ((third.applyOp (subtractionDifferenceOp scratch)).read
    (.storage (subtractionDifferenceOp scratch).outputRef.toCStorageRef)).first = _
  rw [difference]
  change (CShape.subBorrow (width + 1) (.product
    (third.read (reductionRead scratch.augmented)).first
    (third.read (reductionRead scratch.right)))).first = _
  rw [augmented, rightRetained]

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual six-operation record returns the total finite value on the original caller inputs. -/
lemma subBody_value (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (separate : SubSeparation left right scratch)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (subBodyStep (model := model) left right scratch output store).1.read (reductionRead output) =
      subValue (store.read left) (store.read right) (store.read (reductionRead scratch.modulus)) :=
    by
  change (reduceWordStep (.first (reductionRead scratch.difference))
    (reductionRead scratch.modulus) output (subStore left right scratch store)).1.read
      (reductionRead output) = _
  rw [reduceWord_value, subStore_difference left right scratch separate store,
    subStore_preserves left right scratch store (reductionRead scratch.modulus) separate.modulus]
  rfl

/-- After reduction only the real result changes beyond the four explicit arithmetic writes. -/
lemma subBody_store (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (separate : SubSeparation left right scratch)
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (subBodyStep (model := model) left right scratch output store).1 =
      (subStore left right scratch store).write output
        (subValue (store.read left) (store.read right)
          (store.read (reductionRead scratch.modulus))) := by
  apply Store.store_eq_write_of_read_frame
  · exact subBody_value left right scratch separate output store
  · intro shape other free
    change (reduceWordStep _ (reductionRead scratch.modulus) output
      (subStore left right scratch store)).1.read (.storage other) = _
    apply reduceWord_read_other
    simpa [CInputRef.storageKeys] using free

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
