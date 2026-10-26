/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Sequence

/-!
# Exact protected reads of the original row instruction sequences

Each slot changes only its real output cell. Structural reads outside all
actual output keys retain their entire finite values through the same real
chronological record. No assumption is made about the old output contents.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- The one actual caller cell overwritten by the original slot. -/
def writtenKey (instruction : RowInstruction ctx width length) : StorageKey :=
  match instruction with
  | .add _ _ output | .sub _ _ output | .multiply _ _ output |
      .coefficient _ output => output.key
  | .write array _ _ => array.key

/-- An arbitrary structural read outside the slot's actual output retains its full value. -/
lemma update_read_other (instruction : RowInstruction ctx width length) (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (store : Store ctx)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : instruction.writtenKey ∉ observed.storageKeys) :
    (instruction.update spec modulus store).read observed = store.read observed := by
  cases instruction with
  | add left right output =>
      exact Store.read_write_of_not_mem_storageKeys _ _ _ observed separate
  | sub left right output =>
      exact Store.read_write_of_not_mem_storageKeys _ _ _ observed separate
  | multiply left right output =>
      exact Store.read_write_of_not_mem_storageKeys _ _ _ observed separate
  | coefficient input output =>
      exact Store.read_write_of_not_mem_storageKeys _ _ _ observed separate
  | write array index input =>
      exact Store.read_applyOp_of_not_mem_storageKeys _ _ observed separate

/-- Complete protected values survive every original finite-word update in chronological order. -/
lemma updates_read_other (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (store : Store ctx) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ index, (instructions index).writtenKey ∉ observed.storageKeys) :
    (updates spec modulus count instructions store).read observed = store.read observed := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      exact (ih (fun index => instructions index.succ)
        ((instructions 0).update spec modulus store) (fun index => separate index.succ)).trans
          ((instructions 0).update_read_other spec modulus store observed (separate 0))

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The same complete values survive the actual physical record, including all lexical releases. -/
lemma rangeRecord_read_other (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (before : Store ctx × model.HiddenState) {shape : CShape} (observed : CInputRef ctx shape)
    (separate : ∀ index, (instructions index).writtenKey ∉ observed.storageKeys) :
    (rangeRecord spec modulus environment count instructions before).1.1.read observed =
      before.1.read observed := by
  rw [rangeRecord_store]
  exact updates_read_other spec modulus count instructions before.1 observed separate

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction
