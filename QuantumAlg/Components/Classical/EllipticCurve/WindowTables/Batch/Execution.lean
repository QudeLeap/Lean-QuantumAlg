/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Circuit
import all QuantumAlg.Components.Classical.Modular.NativePower.ScopedLaws
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Coefficient.Semantics

/-!
# Complete actual batch pass execution records

Each prefix write, multiply and denominator overwrite reads the preceding
actual Store. The indexed passes preserve their true paths and all incoming
quantum-reference blocks. These equations do not assume independent rows or
replace the actual XGCD coefficient by a mathematical inverse operation.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame

open Execution Modular.NativePower ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width length : Nat}
  (frame : BatchFrame ctx width length)

/-- The actual prefix write precedes the actual multiply on the returned Store. -/
def forwardRecord (index : Fin length) :
    Store ctx → Store ctx × (frame.forwardStep (model := model) index).Path :=
  Circuit.sequenceStoreRecord
    (BitWord.instruction (execution := model)
      (rowWriteOp frame.prefixes index (wordRead frame.work.product)))
    (scopedMultiply (wordRead frame.work.product) (rowRead frame.denominators index)
      frame.modulus frame.work.product)
    (BitWord.instructionStep (execution := model)
      (rowWriteOp frame.prefixes index (wordRead frame.work.product)))
    (scopedMultiplyStep (wordRead frame.work.product) (rowRead frame.denominators index)
      frame.modulus frame.work.product)

/-- The reverse record reads the original C entry before its final real overwrite. -/
def reverseRecord (index : Fin length) :
    Store ctx → Store ctx × (frame.reverseStep (model := model) index).Path :=
  Circuit.sequenceStoreRecord
    (scopedMultiply (wordRead frame.work.inverse) (rowRead frame.prefixes index)
      frame.modulus frame.work.temporary)
    ((scopedMultiply (wordRead frame.work.inverse) (rowRead frame.denominators index)
      frame.modulus frame.work.inverse).seq
        (BitWord.instruction (execution := model)
          (rowWriteOp frame.denominators index (wordRead frame.work.temporary))))
    (scopedMultiplyStep (wordRead frame.work.inverse) (rowRead frame.prefixes index)
      frame.modulus frame.work.temporary)
    (Circuit.sequenceStoreRecord
      (scopedMultiply (wordRead frame.work.inverse) (rowRead frame.denominators index)
        frame.modulus frame.work.inverse)
      (BitWord.instruction (execution := model)
        (rowWriteOp frame.denominators index (wordRead frame.work.temporary)))
      (scopedMultiplyStep (wordRead frame.work.inverse) (rowRead frame.denominators index)
        frame.modulus frame.work.inverse)
      (BitWord.instructionStep (execution := model)
        (rowWriteOp frame.denominators index (wordRead frame.work.temporary))))

/-- The four forward native instructions preserve all reference and history correlations. -/
lemma forwardStep_execute (index : Fin length) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.forwardStep (model := model) index).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.forwardRecord index entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (fun _ {_} _ initial => BitWord.bitWord_instruction_execute
      (environment := environment) (execution := model) _ initial)
    (nativePower_scopedMultiply_execute _ _ _ _) Reference state

/-- All seven reverse instructions act on the true intermediate Stores in their original order. -/
lemma reverseStep_execute (index : Fin length) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.reverseStep (model := model) index).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.reverseRecord index entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (nativePower_scopedMultiply_execute _ _ _ _)
    (fun reference {_} _ initial =>
      Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
        (nativePower_scopedMultiply_execute _ _ _ _)
        (fun _ {_} _ current => BitWord.bitWord_instruction_execute
          (environment := environment) (execution := model) _ current) reference initial)
    Reference state

/-- Actual forward-pass record, with row zero excluded by construction. -/
def forwardPassRecord (count : Nat) (fits : count < length) :
    Store ctx → Store ctx × (frame.forwardPass (model := model) count fits).Path :=
  Circuit.forRangeStoreRecord count
    (fun index => frame.forwardStep ⟨index.val + 1, by omega⟩)
    (fun index => frame.forwardRecord ⟨index.val + 1, by omega⟩)

/-- Actual decreasing-row record, with every original denominator read before replacement. -/
def reversePassRecord (count : Nat) (fits : count < length) :
    Store ctx → Store ctx × (frame.reversePass (model := model) count fits).Path :=
  Circuit.forRangeStoreRecord count
    (fun index => frame.reverseStep ⟨count - index.val, by omega⟩)
    (fun index => frame.reverseRecord ⟨count - index.val, by omega⟩)

/-- The actual increasing pass retains the complete joint input through its indexed record. -/
lemma forwardPass_execute (count : Nat) (fits : count < length) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.forwardPass (model := model) count fits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.forwardPassRecord count fits entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) count
    (fun index => frame.forwardStep ⟨index.val + 1, by omega⟩)
    (fun index => frame.forwardRecord ⟨index.val + 1, by omega⟩)
    (fun index => frame.forwardStep_execute ⟨index.val + 1, by omega⟩) Reference state

/-- The actual decreasing pass retains every incoming Store overwrite fiber and old history. -/
lemma reversePass_execute (count : Nat) (fits : count < length) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (frame.reversePass (model := model) count fits).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := frame.reversePassRecord count fits entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) count
    (fun index => frame.reverseStep ⟨count - index.val, by omega⟩)
    (fun index => frame.reverseRecord ⟨count - index.val, by omega⟩)
    (fun index => frame.reverseStep_execute ⟨count - index.val, by omega⟩) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.BatchFrame
