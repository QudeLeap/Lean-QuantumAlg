/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import all QuantumAlg.Components.Classical.ConstantWord.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete borrowed restoration of actual native order recovery

Each real arithmetic write is intrinsically writable, and every lexical field
has its matching allocation and release. The actual stored branches and finite
iteration preserve all borrowed classical values. Combined with the sole
interpreter's full-block equation, this restores borrowed classical storage,
borrowed quantum systems and every external reference jointly, for all states.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth candidateWidth : Nat}

private theorem prefix_borrowed (numerator denominator previous older :
    CInputRef ctx (.unsignedWord candidateWidth))
    (division : CWriteRef ctx (cursorDivisionShape candidateWidth))
    (candidate : CWriteRef ctx (.unsignedWord candidateWidth)) (store : Store ctx) :
    ((candidatePrefixStep (model := model) numerator denominator previous older division candidate
      store).1).readBorrowedClassical = store.readBorrowedClassical := by
  simp only [candidatePrefixStep, scopedContinuantStep, Store.readBorrowedClassical_popWorkspace,
    continuantStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    Store.readBorrowedClassical_pushWorkspace]

private theorem selection_borrowed (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth)) (value : CShape.Value .bit)
    (store : Store ctx) :
    (selectionChoiceStep (model := model) cells remainder value store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  cases value with
  | bit value =>
      cases value <;> simp only [selectionChoiceStep, advanceCursorStep, acceptCursorStep,
        BitWord.instructionStep, Store.readBorrowedClassical_applyOp]

private theorem visit_borrowed (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (division : CWriteRef ctx (cursorDivisionShape candidateWidth)) (store : Store ctx) :
    (visitWithDivisionStep (model := model) spec base cells division
      store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [visitWithDivisionStep, selection_borrowed, nativeValidation_borrowed_values,
    prefix_borrowed]

private theorem active_borrowed (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx) :
    (activeVisitStep (model := model) spec base cells store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [activeVisitStep, Store.readBorrowedClassical_popWorkspace, visit_borrowed,
    Store.readBorrowedClassical_pushWorkspace]

private theorem activity_borrowed (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (value : CShape.Value .bit)
    (store : Store ctx) :
    (activityChoiceStep (model := model) spec base cells value store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  cases value with
  | bit value => cases value <;> simp only [activityChoiceStep, active_borrowed]

/-- Every actual activity-gated slot preserves the full borrowed classical value. -/
theorem nativeRecovery_slot_borrowed_values (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx) :
    (scanSlotStep (model := model) spec base cells store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [scanSlotStep, activity_borrowed]

private theorem iteration_borrowed (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (count : Nat) (store : Store ctx) :
    ((fun initial => (scanSlotStep (model := model) spec base cells initial).1)^[count]
      store).readBorrowedClassical =
      store.readBorrowedClassical := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, ih, nativeRecovery_slot_borrowed_values]

private theorem initialization_borrowed (ctx : RuntimeCtx model.kind)
    (modulusWidth phaseBits : Nat)
    (sample : CInputRef ctx (.bits phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    (initializeScanStep (model := model) ctx modulusWidth phaseBits sample
      store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [initializeScanStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    ConstantWord.constantWord_foldStep_borrowed_values,
    TerminalDecode.terminalDecode_foldStep_borrowed_values]

private theorem body_borrowed {phaseBits : Nat}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store (recoveryContext ctx modulusWidth (phaseBits + 1))) :
    (recoveryBodyStep (model := model) spec base sample output store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  simp only [recoveryBodyStep, BitWord.instructionStep, Store.readBorrowedClassical_applyOp,
    iteration_borrowed,
    initialization_borrowed]

omit [BitWord.Selected model] in
private theorem scope_borrowed (ctx : RuntimeCtx model.kind) (modulusWidth candidateWidth : Nat)
    (fields : List RecoveryField)
    (body : Circuit model (fieldsContext ctx modulusWidth candidateWidth fields)
      (fieldsContext ctx modulusWidth candidateWidth fields))
    (step : Store (fieldsContext ctx modulusWidth candidateWidth fields) →
      Store (fieldsContext ctx modulusWidth candidateWidth fields) × body.Path)
    (preserves : ∀ store, (step store).1.readBorrowedClassical = store.readBorrowedClassical)
    (store : Store ctx) :
    ((scopeRecoveryStep ctx modulusWidth candidateWidth fields body step
      store).1).readBorrowedClassical =
      store.readBorrowedClassical := by
  induction fields generalizing ctx with
  | nil => exact preserves store
  | cons field rest ih =>
      simp only [scopeRecoveryStep, Store.readBorrowedClassical_popWorkspace,
        ih _ body step preserves, Store.readBorrowedClassical_pushWorkspace]

/-- Complete recovery preserves all borrowed classical values without an input restriction. -/
theorem nativeRecovery_into_borrowed_values {phaseBits : Nat}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (store : Store ctx) :
    (intoStep (model := model) spec base sample output store).1.readBorrowedClassical =
      store.readBorrowedClassical :=
  scope_borrowed ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)
    (recoveryBodyStep (model := model) spec base sample output)
    (body_borrowed spec base sample output) store

/-- The same complete execution jointly restores all borrowed classical/quantum/reference data. -/
theorem nativeRecovery_into_borrowedRestored {phaseBits : Nat}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) spec base sample output).BorrowedRestored Reference state
      ((into (model := model) spec base sample output).execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, nativeRecovery_into_execute]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := model.HiddenState × History)
    (K := model.HiddenState ×
      (History × (into (model := model) spec base sample output).Path)) state
    (fun entry => ((intoStep (model := model) spec base sample output entry.1).1,
      (entry.2.1, (entry.2.2,
        (intoStep (model := model) spec base sample output entry.1).2))))
    (fun entry => nativeRecovery_into_borrowed_values spec base sample output entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
