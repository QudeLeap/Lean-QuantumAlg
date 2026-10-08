/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Initialization
import all QuantumAlg.Components.Classical.Modular.NativePower.Bit.Semantics
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopeExecution
import all QuantumAlg.Components.Classical.ConstantWord.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete borrowed restoration of actual modular power

Every write names an intrinsically writable original result or a real lexical
scratch cell. The complete borrowed classical value is therefore unchanged.
The actual interpreter's full-block equation upgrades this to joint borrowed
classical, quantum and external-reference restoration, without a state promise
or an input-dependent exception.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

private theorem scoped_borrowed (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (scopedMultiplyStep (model := model) left right modulus output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [scopedMultiplyStep, leaveMultiply, multiplyStep, BitWord.instructionStep,
    enterMultiply,
    Store.readBorrowedClassical_popWorkspace, Store.readBorrowedClassical_applyOp,
    Store.readBorrowedClassical_pushWorkspace]

private theorem choice_borrowed (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (store : Store ctx) :
    (multiplyChoiceStep (model := model) base modulus output value store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  cases value with
  | bit bit => cases bit <;> simp only [multiplyChoiceStep, scoped_borrowed]

private theorem bit_borrowed (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bit : CInputRef ctx .bit)
    (store : Store ctx) :
    (bitStep (model := model) base modulus output bit store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [bitStep, choice_borrowed, scoped_borrowed]

/-- The entire actual exponent fold preserves every borrowed classical value. -/
theorem nativePower_fold_borrowed_values (base : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) (bits : List (CInputRef ctx .bit))
    (store : Store ctx) :
    (foldStep (model := model) base modulus output bits store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  induction bits generalizing store with
  | nil => rfl
  | cons bit rest ih =>
      change ((foldStep (model := model) base modulus output rest
        (bitStep (model := model) base modulus output bit store).1).1).readBorrowedClassical = _
      rw [ih, bit_borrowed]

private theorem body_borrowed (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (powerCtx ctx width)) :
    (powerBodyStep (model := model) spec base exponent output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [powerBodyStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    nativePower_fold_borrowed_values,
    ConstantWord.constantWord_foldStep_borrowed_values]

/-- Actual allocation and release preserve the complete outer borrowed classical value. -/
theorem nativePower_into_borrowed_values (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep (model := model) spec base exponent output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [intoStep, leavePower, Store.readBorrowedClassical_popWorkspace, body_borrowed,
    enterPower, Store.readBorrowedClassical_pushWorkspace]

/-- Only the declared outer destination can change among the original structural reads. -/
theorem nativePower_into_read_other (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) :
    ((intoStep (model := model) spec base exponent output store).1).read other =
      store.read other := by
  have oldFree : (writeUnderPower output width).key ∉ (underPower other width).storageKeys := by
    rw [nativePower_underPower_keys]
    exact separate
  have accumulatorFree := (nativePower_input_separation other width).2.2
  unfold intoStep
  rw [nativePower_leavePower_read]
  unfold powerBodyStep
  simp only [BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (copyResultOp output)
    (underPower other width) oldFree]
  rw [nativePower_fold_read_other (model := model) _ _ _ _ (underPower other width) accumulatorFree]
  exact nativePower_initialized_read_original (model := model) spec base store other

/-- The same actual execution jointly restores all borrowed storage and every external reference. -/
theorem nativePower_into_borrowedRestored (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) spec base exponent output).BorrowedRestored Reference state
      ((into (model := model) spec base exponent output).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, nativePower_into_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState ×
      (History × (into (model := model) spec base exponent output).Path)) state
    (fun entry => ((intoStep (model := model) spec base exponent output entry.1).1,
      (entry.2.1, (entry.2.2, (intoStep (model := model) spec base exponent output entry.1).2))))
    (fun entry => nativePower_into_borrowed_values (model := model) spec base exponent output
      entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
