/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Decision.Values

/-!
# Values of the actual unique-free-word decision

The original decrement and mask write the real work word before the two
stored equality decisions. The source called zero remains an arbitrary
word; no zero value, positive width or initial success is assumed. The
surrounding real word and bit scopes supply the local separation facts.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem test_read_word (reject : Bool)
    (left right : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (store : Store ctx) {size : Nat} (word : CWriteRef ctx (.unsignedWord size)) :
    (decisionTestStep reject left right success flag store).1.read
      (.storage word.toCStorageRef) = store.read (.storage word.toCStorageRef) :=
  gf2DecisionTest_read_other reject left right success flag store _
    (avoids success word (shapes_ne success word (by intro same; cases same)))
    (avoids flag word (shapes_ne flag word (by intro same; cases same)))

private theorem masked_read_other
    (free work : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (separate : work.key ∉ other.storageKeys) :
    ((store.applyOp (decisionDecrementOp free work)).applyOp
      (decisionMaskOp free work)).read other = store.read other := by
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (decisionMaskOp free work) other separate,
    Store.read_applyOp_of_not_mem_storageKeys _ (decisionDecrementOp free work) other separate]

/-- The real two decisions retain success exactly when both original word tests hold. -/
theorem gf2UniqueFreeBody_success
    (free zero work : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (workFree : work.key ≠ free.key) (workZero : work.key ≠ zero.key)
    (flagSuccess : flag.key ≠ success.key) (store : Store ctx) :
    ((uniqueFreeBodyStep free zero work success flag store).1.read
      (.storage success.toCStorageRef)).toBool =
      ((store.read (.storage success.toCStorageRef)).toBool &&
        decide ((CShape.wordBitAnd width (store.read (.storage free.toCStorageRef))
          (CShape.wordSub width (store.read (.storage free.toCStorageRef))
            (CShape.wordOfNat width 1))).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat) &&
        !decide ((store.read (.storage free.toCStorageRef)).toNat =
          (store.read (.storage zero.toCStorageRef)).toNat)) := by
  let decremented := store.applyOp (decisionDecrementOp free work)
  let masked := decremented.applyOp (decisionMaskOp free work)
  have freeFirst : decremented.read (.storage free.toCStorageRef) =
      store.read (.storage free.toCStorageRef) :=
    Store.read_applyOp_of_not_mem_storageKeys store (decisionDecrementOp free work) _
      (avoids work free workFree)
  have workFirst : decremented.read (.storage work.toCStorageRef) =
      CShape.wordSub width (store.read (.storage free.toCStorageRef))
        (CShape.wordOfNat width 1) :=
    Store.read_applyOp_output store (decisionDecrementOp free work)
  have workMasked : masked.read (.storage work.toCStorageRef) =
      CShape.wordBitAnd width (store.read (.storage free.toCStorageRef))
        (CShape.wordSub width (store.read (.storage free.toCStorageRef))
          (CShape.wordOfNat width 1)) := by
    refine (Store.read_applyOp_output decremented (decisionMaskOp free work)).trans ?_
    change CShape.wordBitAnd width (decremented.read (.storage free.toCStorageRef))
      (decremented.read (.storage work.toCStorageRef)) = _
    rw [freeFirst, workFirst]
  have freeMasked : masked.read (.storage free.toCStorageRef) =
      store.read (.storage free.toCStorageRef) :=
    masked_read_other free work store _ (avoids work free workFree)
  have zeroMasked : masked.read (.storage zero.toCStorageRef) =
      store.read (.storage zero.toCStorageRef) :=
    masked_read_other free work store _ (avoids work zero workZero)
  have successMasked : masked.read (.storage success.toCStorageRef) =
      store.read (.storage success.toCStorageRef) :=
    masked_read_other free work store _
      (avoids work success (shapes_ne work success (by intro same; cases same)))
  change ((decisionTestStep true free zero success flag
    (decisionTestStep false work zero success flag masked).1).1.read _).toBool = _
  rw [gf2DecisionTest_success true free zero success flag flagSuccess,
    test_read_word false work zero success flag masked free,
    test_read_word false work zero success flag masked zero,
    gf2DecisionTest_success false work zero success flag flagSuccess,
    workMasked, freeMasked, zeroMasked, successMasked]
  simp

/-- Only the real work word, success bit and equality latch can change a structural read. -/
theorem gf2UniqueFreeBody_read_other
    (free zero work : CWriteRef ctx (.unsignedWord width)) (success flag : CWriteRef ctx .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (workFree : work.key ∉ other.storageKeys)
    (successFree : success.key ∉ other.storageKeys) (flagFree : flag.key ∉ other.storageKeys) :
    (uniqueFreeBodyStep free zero work success flag store).1.read other = store.read other := by
  change (decisionTestStep true free zero success flag
    (decisionTestStep false work zero success flag
      ((store.applyOp (decisionDecrementOp free work)).applyOp
        (decisionMaskOp free work))).1).1.read other = _
  rw [gf2DecisionTest_read_other true free zero success flag _ other successFree flagFree,
    gf2DecisionTest_read_other false work zero success flag _ other successFree flagFree]
  exact masked_read_other free work store other workFree

end

end QuantumAlg.ClassicalRoutines.GF2.Native
