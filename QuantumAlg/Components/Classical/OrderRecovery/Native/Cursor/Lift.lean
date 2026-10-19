/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor.Representation

/-!
# Exact cursor observations under the real division allocation

Each observation is preserved by the existing structural reference lift and
the actual workspace initialization. The finite scan also preserves all
source comparison reads and stops changing the complete store once its
actual activity bit is false.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- The real workspace push preserves the four observed cursor coordinates. -/
lemma nativeScan_cursorReads_underWorkspace {width : Nat}
    (cells : CursorCells ctx width) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : CursorReads cells store cursor)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CursorReads (cells.underWorkspace key shape fresh)
      (store.pushWorkspace key shape fresh) cursor := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (congrArg CShape.Value.toNat (Store.read_pushWorkspace_underWorkspace
      store key shape fresh (cellRead cells.numerator))).trans reads.numerator
  · exact (congrArg CShape.Value.toNat (Store.read_pushWorkspace_underWorkspace
      store key shape fresh (cellRead cells.denominator))).trans reads.denominator
  · exact (congrArg CShape.Value.toNat (Store.read_pushWorkspace_underWorkspace
      store key shape fresh (cellRead cells.older))).trans reads.older
  · exact (congrArg CShape.Value.toNat (Store.read_pushWorkspace_underWorkspace
      store key shape fresh (cellRead cells.previous))).trans reads.previous

/-- The actual pending latches and cursor remain the same under that allocation. -/
lemma nativeScan_pendingReads_underWorkspace
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx)
    (cursor : ClassicalAlgorithms.OrderRecovery.EuclideanContinuantCursor)
    (reads : PendingCursorReads cells store cursor)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    PendingCursorReads (cells.underWorkspace key shape fresh)
      (store.pushWorkspace key shape fresh) cursor := by
  refine ⟨nativeScan_cursorReads_underWorkspace cells.cursor store cursor
    reads.toCursorReads key shape fresh, ?_, ?_⟩
  · exact (Store.read_pushWorkspace_underWorkspace store key shape fresh
      (cellRead cells.cursor.active)).trans reads.active
  · exact (Store.read_pushWorkspace_underWorkspace store key shape fresh
      (cellRead cells.accepted)).trans reads.accepted

/-- The real base, zero and one reads keep their source values under the same workspace. -/
lemma nativeScan_sourceReads_underWorkspace
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx)
    (reads : ScanSourceReads spec input base cells store)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    ScanSourceReads spec input (base.underWorkspace key shape fresh)
      (cells.underWorkspace key shape fresh) (store.pushWorkspace key shape fresh) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Store.read_pushWorkspace_underWorkspace store key shape fresh base).trans reads.baseValue
  · exact (congrArg CShape.Value.toNat
      (Store.read_pushWorkspace_underWorkspace store key shape fresh cells.zero)).trans
        reads.zeroValue
  · exact (congrArg CShape.Value.toNat
      (Store.read_pushWorkspace_underWorkspace store key shape fresh cells.one)).trans
        reads.oneValue

/-- Every number of real finite slots preserves the source base and comparison constants. -/
lemma nativeScan_iterate_source_reads {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (store : Store ctx) (reads : ScanSourceReads spec input base cells store) (fuel : Nat) :
    ScanSourceReads spec input base cells
      ((fun initial => (scanSlotStep (model := model) spec.modulusSpec base cells initial).1)^[fuel]
        store) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (nativeScan_iterate_read_other spec.modulusSpec base cells fuel
      base baseFree store).trans reads.baseValue
  · exact (congrArg CShape.Value.toNat
      (nativeScan_iterate_read_other spec.modulusSpec base cells fuel cells.zero
        separated.zeroFree store)).trans reads.zeroValue
  · exact (congrArg CShape.Value.toNat
      (nativeScan_iterate_read_other spec.modulusSpec base cells fuel cells.one
        separated.oneFree store)).trans reads.oneValue

/-- A false actual activity bit makes every remaining slot identity on the whole store. -/
lemma nativeScan_iterate_of_inactive {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx)
    (inactive : store.read (cellRead cells.cursor.active) = .bit false) (fuel : Nat) :
    (fun initial => (scanSlotStep (model := model) spec base cells initial).1)^[fuel] store =
      store := by
  have fixed := nativeScan_slot_inactive (model := model)
    spec base cells store inactive
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, fixed, ih]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
