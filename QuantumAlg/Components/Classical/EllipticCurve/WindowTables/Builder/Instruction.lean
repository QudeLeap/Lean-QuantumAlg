/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Add.Record
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Shared.Sub.Correctness
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Store

/-!
# Literal arithmetic instructions of the five-table rows

This syntax names the existing paid row instructions. Its interpretation
uses the same actual shared-modulus arithmetic, raw coefficient computation
and structural vector write. The total Store interpreter records finite
word arithmetic on the preceding Store, including all operand aliases.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

open Execution Modular.NativePower ClassicalAlgorithms.Modular

variable {kind : ProblemKind}

/-- Existing row operations with literal storage references and no semantic value parameters. -/
inductive RowInstruction (ctx : RuntimeCtx kind) (width length : Nat) where
  | add (left right : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.unsignedWord width))
  | sub (left right : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.unsignedWord width))
  | multiply (left right : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.unsignedWord width))
  | coefficient (input : CInputRef ctx (.unsignedWord width))
      (output : CWriteRef ctx (.unsignedWord width))
  | write (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
      (index : Fin length) (input : CInputRef ctx (.unsignedWord width))

namespace RowInstruction

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {width length : Nat}

/-- The literal paid finite-word effect, evaluated on the actual chronological Store. -/
def update {ctx : RuntimeCtx kind} (instruction : RowInstruction ctx width length)
    (spec : ModulusSpec width) (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (store : Store ctx) : Store ctx :=
  match instruction with
  | .add left right output => store.write output
      (Field.Native.Shared.addValue (store.read left) (store.read right)
        (store.read (wordRead modulus)))
  | .sub left right output => store.write output
      (Field.Native.Shared.subValue (store.read left) (store.read right)
        (store.read (wordRead modulus)))
  | .multiply left right output => store.write output
      (multiplyValue (store.read left) (store.read right) (store.read (wordRead modulus)))
  | .coefficient input output => store.write output
      (CShape.wordOfNat width (Field.Native.coefficientResidue spec (store.read input)).val)
  | .write array index input => store.applyOp (rowWriteOp array index input)

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Every named slot lowers to its original actual circuit, without an extra operation. -/
def circuit (instruction : RowInstruction ctx width length) (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) : Circuit model ctx ctx :=
  match instruction with
  | .add left right output => Field.Native.Shared.addIntoWord left right (wordRead modulus) output
  | .sub left right output => Field.Native.Shared.subIntoWord left right modulus output
  | .multiply left right output => scopedMultiply left right (wordRead modulus) output
  | .coefficient input output => Field.Native.coefficientIntoWord spec input output
  | .write array index input => BitWord.instruction (execution := model)
      (rowWriteOp array index input)

/-- Actual paths and service states of each original slot, including the real XGCD slot. -/
def record (instruction : RowInstruction ctx width length) (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment) :
    Store ctx × model.HiddenState → (Store ctx × model.HiddenState) ×
      (instruction.circuit (model := model) spec modulus).Path :=
  match instruction with
  | .add left right output => Circuit.preserveHiddenRecord
      (Field.Native.Shared.addIntoWordStep (environment := environment)
        left right (wordRead modulus) output)
  | .sub left right output => Circuit.preserveHiddenRecord
      (Field.Native.Shared.subIntoWordStep (environment := environment) left right modulus output)
  | .multiply left right output => Circuit.preserveHiddenRecord
      (scopedMultiplyStep left right (wordRead modulus) output)
  | .coefficient input output => Field.Native.coefficientIntoWordStep
      (environment := environment) spec input output
  | .write array index input => Circuit.preserveHiddenRecord
      (BitWord.instructionStep (execution := model) (rowWriteOp array index input))

/-- The total finite-word update is the Store of this same actual physical execution record. -/
lemma record_store (instruction : RowInstruction ctx width length) (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (before : Store ctx × model.HiddenState) :
    (instruction.record spec modulus environment before).1.1 =
      instruction.update spec modulus before.1 := by
  cases instruction with
  | add left right output =>
      exact Field.Native.Shared.sharedAddIntoWordStep_store left right (wordRead modulus)
        output before.1
  | sub left right output =>
      exact Field.Native.Shared.sharedSubIntoWordStep_store left right modulus output before.1
  | multiply left right output =>
      exact scopedMultiplyStep_store left right (wordRead modulus) output before.1
  | coefficient input output =>
      exact Field.Native.coefficientIntoWordStep_store spec input output before.1 before.2
  | write array index input => rfl

/-- Every original quantum-reference block and prior history uses the same chronological record. -/
lemma circuit_execute (instruction : RowInstruction ctx width length) (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (instruction.circuit (model := model) spec modulus).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := instruction.record spec modulus environment (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  cases instruction with
  | add left right output =>
      exact Field.Native.Shared.sharedAddIntoWord_execute left right (wordRead modulus)
        output Reference state
  | sub left right output =>
      exact Field.Native.Shared.sharedSubIntoWord_execute left right modulus output Reference state
  | multiply left right output =>
      exact nativePower_scopedMultiply_execute left right (wordRead modulus) output Reference state
  | coefficient input output =>
      exact Field.Native.coefficientIntoWord_execute spec input output Reference state
  | write array index input =>
      exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model)
        (rowWriteOp array index input) state

end

end RowInstruction

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
