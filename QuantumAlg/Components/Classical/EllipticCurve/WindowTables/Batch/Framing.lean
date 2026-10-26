/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Correctness

/-!
# Complete protected reads of the actual batch-inverse record

The increasing traversal, real XGCD coefficient and decreasing traversal
change only C, D and their three working scalars. Every other structural
read, including both coordinate arrays and supplied constant/base words,
retains its exact original value through the same complete actual record.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}

/-- The complete original forward traversal preserves each structurally protected caller read. -/
lemma forwardPassRecord_read_other (frame : BatchFrame ctx width length)
    (count : Nat) (fits : count < length) {shape : CShape} (observed : CInputRef ctx shape)
    (prefixFree : frame.prefixes.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys) (store : Store ctx) :
    (frame.forwardPassRecord (model := model) count fits store).1.read observed =
      store.read observed :=
  Circuit.forRangeStoreRecord_invariant count
    (fun index => frame.forwardStep (model := model) ⟨index.val + 1, by omega⟩)
    (fun index => frame.forwardRecord (model := model) ⟨index.val + 1, by omega⟩)
    (fun _ current => current.read observed = store.read observed)
    (fun index current established =>
      (frame.forwardRecord_read_other ⟨index.val + 1, by omega⟩ observed prefixFree productFree
        current).trans established) store rfl

/-- The complete original decreasing traversal preserves each structurally protected caller read. -/
lemma reversePassRecord_read_other (frame : BatchFrame ctx width length)
    (count : Nat) (fits : count < length) {shape : CShape} (observed : CInputRef ctx shape)
    (denominatorFree : frame.denominators.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys) (store : Store ctx) :
    (frame.reversePassRecord (model := model) count fits store).1.read observed =
      store.read observed :=
  Circuit.forRangeStoreRecord_invariant count
    (fun index => frame.reverseStep (model := model) ⟨count - index.val, by omega⟩)
    (fun index => frame.reverseRecord (model := model) ⟨count - index.val, by omega⟩)
    (fun _ current => current.read observed = store.read observed)
    (fun index current established =>
      (frame.reverseRecord_read_other ⟨count - index.val, by omega⟩ observed denominatorFree
        inverseFree temporaryFree current).trans established) store rfl

/-- The actual original nonempty batch retains all reads outside its five real output cells. -/
lemma nonemptyValueRecord_read_other (frame : BatchFrame ctx width length)
    (spec : ModulusSpec width) (environment : model.Environment)
    (count : Nat) (fits : count < length) {shape : CShape} (observed : CInputRef ctx shape)
    (prefixFree : frame.prefixes.key ∉ observed.storageKeys)
    (productFree : frame.work.product.key ∉ observed.storageKeys)
    (denominatorFree : frame.denominators.key ∉ observed.storageKeys)
    (inverseFree : frame.work.inverse.key ∉ observed.storageKeys)
    (temporaryFree : frame.work.temporary.key ∉ observed.storageKeys)
    (before : Store ctx × model.HiddenState) :
    (frame.nonemptyValueRecord (environment := environment) spec count fits before).1.1.read
      observed = before.1.read observed := by
  let initialized := frame.initializeStore before.1
  let forward := frame.forwardPassRecord (model := model) count fits initialized
  let inverted := Field.Native.coefficientIntoWordStep (environment := environment) spec
    (wordRead frame.work.product) frame.work.inverse (forward.1, before.2)
  change (frame.reversePassRecord (model := model) count fits inverted.1.1).1.read observed = _
  rw [frame.reversePassRecord_read_other count fits observed denominatorFree inverseFree
    temporaryFree]
  rw [Field.Native.coefficientIntoWord_read_other (environment := environment) spec
    (wordRead frame.work.product) frame.work.inverse observed inverseFree forward.1 before.2,
    frame.forwardPassRecord_read_other count fits observed prefixFree productFree initialized,
    frame.initializeStore_read_other observed productFree]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
