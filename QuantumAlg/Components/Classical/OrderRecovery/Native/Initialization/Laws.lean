/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initialization.Frame
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Initial.Readout

/-!
# Actual initial values of the finite order-recovery cursor

The real sampled word supplies the numerator, the dyadic literal supplies its
denominator, and the two actual increments supply the predecessor and modular
one. The activation bit comes from the genuinely fresh false accepted latch.
The resulting claims concern reads of the existing initialization execution.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private theorem loaded_field (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx)
    (index : Fin recoveryFields.length) (notNumerator : (2 : Fin recoveryFields.length) ≠ index)
    (notDenominator : (3 : Fin recoveryFields.length) ≠ index) :
    (initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).read
        (cellRead (recoveryFieldCell ctx modulusWidth (phaseBits + 1) recoveryFields index)) =
      CShape.initialValue
        (recoveryFieldShape modulusWidth (phaseBits + 1) (recoveryFields.get index)) := by
  rw [nativeRecovery_initialLoaded_read_other (model := model) modulusWidth phaseBits sample _ _
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1)
      2 index notNumerator)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1)
      3 index notDenominator)]
  exact nativeRecovery_enter_field modulusWidth (phaseBits + 1) recoveryFields index store

/-- Initialization writes exactly the original measured full-register numerator. -/
theorem nativeRecovery_initialized_numerator (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    ((initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator)).toNat =
      (ClassicalAlgorithms.OrderRecovery.fullRegisterIndex
        (fun bit => ((store.read sample).bitGet bit).toBool)).val := by
  rw [nativeRecovery_initialize_store]
  rw [nativeRecovery_initialFinish_read_other (ctx := ctx) modulusWidth phaseBits _
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 4 2 (by decide))
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 1 2 (by decide))
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 8 2 (by decide))]
  unfold initializationLoadedStore
  rw [ConstantWord.constantWord_fold_read_other
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator _
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 3 2 (by decide))]
  exact nativeRecovery_decoded_numerator (model := model) modulusWidth phaseBits sample store

/-- The widened denominator contains the complete dyadic cardinality at every phase width. -/
theorem nativeRecovery_initialized_denominator (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    ((initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator)).toNat =
      2 ^ phaseBits := by
  rw [nativeRecovery_initialize_store]
  rw [nativeRecovery_initialFinish_read_other (ctx := ctx) modulusWidth phaseBits _
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 4 3 (by decide))
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 1 3 (by decide))
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 8 3 (by decide))]
  have fits : 2 ^ phaseBits < 2 ^ (phaseBits + 1) := by
    rw [Nat.pow_succ]
    have positive := Nat.two_pow_pos phaseBits
    omega
  exact (ConstantWord.constantWord_read
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator (2 ^ phaseBits)
    _).trans (Nat.mod_eq_of_lt fits)

/-- The actual older-continuant increment writes the canonical encoding of one. -/
theorem nativeRecovery_initialized_older (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older) =
      CShape.wordOfNat (phaseBits + 1) 1 := by
  rw [nativeRecovery_initialize_store]
  unfold initializationFinishStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeActiveOp ctx modulusWidth phaseBits)
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 8 4 (by decide))]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeOneOp ctx modulusWidth phaseBits)
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 1 4 (by decide))]
  have actual := Store.read_applyOp_output
    (initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store))
    (initializeOlderOp ctx modulusWidth phaseBits)
  change _ = CShape.wordOfNat (phaseBits + 1)
    (((initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older)).toNat + 1)
      at actual
  refine actual.trans ?_
  have zero := loaded_field (model := model)
    modulusWidth phaseBits sample store 4 (by decide) (by decide)
  change (initializationLoadedStore (model := model) modulusWidth phaseBits sample
    (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).read
      (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.older) =
        CShape.wordOfNat (phaseBits + 1) 0 at zero
  rw [zero]
  simp only [CShape.wordOfNat_val, Nat.zero_mod, Nat.zero_add]

/-- The actual modular-one increment writes one modulo its declared word capacity. -/
theorem nativeRecovery_initialized_one (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (recoveryCells ctx modulusWidth (phaseBits + 1)).one =
      CShape.wordOfNat modulusWidth 1 := by
  rw [nativeRecovery_initialize_store]
  unfold initializationFinishStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeActiveOp ctx modulusWidth phaseBits)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).one
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 8 1 (by decide))]
  have actual := Store.read_applyOp_output
    ((initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).applyOp
        (initializeOlderOp ctx modulusWidth phaseBits))
    (initializeOneOp ctx modulusWidth phaseBits)
  change _ = CShape.wordOfNat modulusWidth
    ((((initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).applyOp
        (initializeOlderOp ctx modulusWidth phaseBits)).read
          (recoveryCells ctx modulusWidth (phaseBits + 1)).one).toNat + 1) at actual
  refine actual.trans ?_
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeOlderOp ctx modulusWidth phaseBits)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).one
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 4 1 (by decide))]
  have zero := loaded_field (model := model)
    modulusWidth phaseBits sample store 1 (by decide) (by decide)
  change (initializationLoadedStore (model := model) modulusWidth phaseBits sample
    (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).read
      (recoveryCells ctx modulusWidth (phaseBits + 1)).one =
        CShape.wordOfNat modulusWidth 0 at zero
  rw [zero]
  simp only [CShape.wordOfNat_val, Nat.zero_mod, Nat.zero_add]

/-- Negating the real false accepted latch actually activates the first visit. -/
theorem nativeRecovery_initialized_active (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits)) (store : Store ctx) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).1.read
        (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.active) =
      .bit true := by
  rw [nativeRecovery_initialize_store]
  unfold initializationFinishStore
  have actual := Store.read_applyOp_output
    (((initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).applyOp
        (initializeOlderOp ctx modulusWidth phaseBits)).applyOp
          (initializeOneOp ctx modulusWidth phaseBits))
    (initializeActiveOp ctx modulusWidth phaseBits)
  change _ = Resource.BitOpcode.eval .not
    ((((initializationLoadedStore (model := model) modulusWidth phaseBits sample
      (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).applyOp
        (initializeOlderOp ctx modulusWidth phaseBits)).applyOp
          (initializeOneOp ctx modulusWidth phaseBits)).read
            (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)) at actual
  refine actual.trans ?_
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeOneOp ctx modulusWidth phaseBits)
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 1 9 (by decide))]
  rw [Store.read_applyOp_of_not_mem_storageKeys _
    (initializeOlderOp ctx modulusWidth phaseBits)
    (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted)
    (nativeRecovery_field_read_separate (ctx := ctx) modulusWidth (phaseBits + 1) 4 9 (by decide))]
  have acceptedFalse := loaded_field (model := model)
    modulusWidth phaseBits sample store 9 (by decide) (by decide)
  change (initializationLoadedStore (model := model) modulusWidth phaseBits sample
    (enterRecoveryFields modulusWidth (phaseBits + 1) recoveryFields store)).read
      (cellRead (recoveryCells ctx modulusWidth (phaseBits + 1)).accepted) =
        .bit false at acceptedFalse
  rw [acceptedFalse]
  rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
