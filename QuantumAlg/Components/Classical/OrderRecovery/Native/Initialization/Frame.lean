/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Layout.Keys

/-!
# Exact storage frames of recovery initialization

The decoder, literal loader and three final instructions write their actual
five destinations. Structural input reads and every other freshly allocated
field retain their exact original values throughout this same execution.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The actual store immediately after the decoder and dyadic literal loader. -/
def initializationLoadedStore (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    Store (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  (ConstantWord.foldStep (model := model)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
    (List.ofFn (ConstantWord.constantBits (phaseBits + 1) (2 ^ phaseBits)))
    (TerminalDecode.foldStep (model := model)
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator
      (List.ofFn (initialPhaseBitRefs ctx modulusWidth phaseBits sample)) store).1).1

/-- The final three actual elementary initialization writes. -/
def initializationFinishStore {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (modulusWidth phaseBits : Nat)
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    Store (recoveryContext ctx modulusWidth (phaseBits + 1)) :=
  ((store.applyOp (initializeOlderOp ctx modulusWidth phaseBits)).applyOp
    (initializeOneOp ctx modulusWidth phaseBits)).applyOp
      (initializeActiveOp ctx modulusWidth phaseBits)

/-- These named intermediate stores are exactly the existing initialization record. -/
theorem nativeRecovery_initialize_store (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample store).1 =
      initializationFinishStore modulusWidth phaseBits
        (initializationLoadedStore (model := model) modulusWidth phaseBits sample store) := by
  rfl

/-- Different real field positions are separate actual reads and writes. -/
theorem nativeRecovery_field_read_separate {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (modulusWidth candidateWidth : Nat)
    (written observed : Fin recoveryFields.length) (different : written ≠ observed) :
    (recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields written).key ∉
      (cellRead
        (recoveryFieldCell ctx modulusWidth candidateWidth recoveryFields observed)).storageKeys :=
    by
  intro present
  exact different (nativeRecovery_field_injective modulusWidth candidateWidth recoveryFields
    (List.mem_singleton.mp present))

/-- The actual decoder and loader preserve reads outside their two destinations. -/
theorem nativeRecovery_initialLoaded_read_other (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1)))
    {shape : CShape} (other : CInputRef (recoveryContext ctx modulusWidth (phaseBits + 1)) shape)
    (numeratorFree :
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator.key ∉ other.storageKeys)
    (denominatorFree :
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator.key ∉ other.storageKeys) :
    (initializationLoadedStore (model := model) modulusWidth phaseBits sample store).read other =
      store.read other := by
  unfold initializationLoadedStore
  exact (ConstantWord.constantWord_fold_read_other _ _ other denominatorFree _).trans
    (TerminalDecode.terminalDecode_fold_read_other _ _ store other numeratorFree)

/-- The final three actual instructions preserve all other structural reads. -/
theorem nativeRecovery_initialFinish_read_other {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (modulusWidth phaseBits : Nat)
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1)))
    {shape : CShape} (other : CInputRef (recoveryContext ctx modulusWidth (phaseBits + 1)) shape)
    (olderFree :
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older.key ∉ other.storageKeys)
    (oneFree : (recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields 1).key ∉
      other.storageKeys)
    (activeFree :
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.active.key ∉ other.storageKeys) :
    (initializationFinishStore modulusWidth phaseBits store).read other = store.read other := by
  unfold initializationFinishStore
  exact (Store.read_applyOp_of_not_mem_storageKeys _
    (initializeActiveOp ctx modulusWidth phaseBits) other activeFree).trans
      ((Store.read_applyOp_of_not_mem_storageKeys _
        (initializeOneOp ctx modulusWidth phaseBits) other oneFree).trans
          (Store.read_applyOp_of_not_mem_storageKeys store
            (initializeOlderOp ctx modulusWidth phaseBits) other olderFree))

/-- Initialization preserves every original stored input, including the actual modular base. -/
theorem nativeRecovery_initialize_read_original (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields other) =
      store.read other := by
  rw [nativeRecovery_initialize_store]
  rw [nativeRecovery_initialFinish_read_other modulusWidth phaseBits _ _
    (nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 4 other)
    (nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 1 other)
    (nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 8 other)]
  rw [nativeRecovery_initialLoaded_read_other modulusWidth phaseBits sample _ _
    (nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 2 other)
    (nativeRecovery_field_input_separate modulusWidth (phaseBits + 1) recoveryFields 3 other)]
  exact nativeRecovery_enter_read modulusWidth (phaseBits + 1) recoveryFields store other

/-- Every unwritten field still reads the canonical value of its genuine workspace head. -/
theorem nativeRecovery_initialize_unwritten_field (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (index : Fin recoveryFields.length)
    (untouched : index ∉ ([2, 3, 4, 1, 8] : List (Fin recoveryFields.length))) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields index)) =
      CShape.initialValue
        (recoveryFieldShape modulusWidth (phaseBits + 1) (recoveryFields.get index)) := by
  have different (written : Fin recoveryFields.length)
      (member : written ∈ ([2, 3, 4, 1, 8] : List (Fin recoveryFields.length))) :
      written ≠ index := by
    intro same
    exact untouched (same ▸ member)
  rw [nativeRecovery_initialize_store]
  rw [nativeRecovery_initialFinish_read_other modulusWidth phaseBits _ _
    (nativeRecovery_field_read_separate modulusWidth (phaseBits + 1) 4 index
      (different 4 (by decide)))
    (nativeRecovery_field_read_separate modulusWidth (phaseBits + 1) 1 index
      (different 1 (by decide)))
    (nativeRecovery_field_read_separate modulusWidth (phaseBits + 1) 8 index
      (different 8 (by decide)))]
  rw [nativeRecovery_initialLoaded_read_other modulusWidth phaseBits sample _ _
    (nativeRecovery_field_read_separate modulusWidth (phaseBits + 1) 2 index
      (different 2 (by decide)))
    (nativeRecovery_field_read_separate modulusWidth (phaseBits + 1) 3 index
      (different 3 (by decide)))]
  exact nativeRecovery_enter_field modulusWidth (phaseBits + 1) recoveryFields index store

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
