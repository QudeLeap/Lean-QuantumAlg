/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Actual original raw field addition

Both operands are widened before the original add-with-carry instruction.
Only then does loaded reduction allocate and materialize its modulus. The
three original arithmetic cells and the later reduction scopes are actual
lexical workspaces; no caller initialization or modulus word is requested.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original widened operands and complete low-word/carry result. -/
structure AddScratch (ctx : RuntimeCtx kind) (width : Nat) where
  left : CWriteRef ctx (.unsignedWord (width + 1))
  right : CWriteRef ctx (.unsignedWord (width + 1))
  sum : CWriteRef ctx (.product (.unsignedWord (width + 1)) .bit)

/-- Deepest-first cell order allocates left, right and sum in the original order. -/
def additionShapes (width : Nat) : List CShape :=
  [.product (.unsignedWord (width + 1)) .bit,
    .unsignedWord (width + 1), .unsignedWord (width + 1)]

/-- Actual references retain the original left, right and sum roles. -/
def additionScratch (cells : Cells ctx (additionShapes width)) : AddScratch ctx width :=
  ⟨cells.tail.tail.head.ref, cells.tail.head.ref, cells.head.ref⟩

/-- Original lossless one-bit widening of the left raw operand. -/
def additionLeftOp (left : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx left scratch.left

/-- Original one-bit widening of the right raw operand, after the left snapshot. -/
def additionRightOp (right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx right scratch.right

/-- Original actual widened add-with-carry operation. -/
def additionSumOp (scratch : AddScratch ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.product (.unsignedWord (width + 1)) .bit) ctx ctx :=
  .addCarry (width + 1) ctx
    (.product (Modular.Reduce.Native.reductionRead scratch.left)
      (Modular.Reduce.Native.reductionRead scratch.right)) scratch.sum

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The three original arithmetic operations precede all reduction preparation. -/
def additionStage (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) : Fin 3 → Circuit model ctx ctx :=
  ![BitWord.instruction (execution := model) (additionLeftOp left scratch),
    BitWord.instruction (execution := model) (additionRightOp right scratch),
    BitWord.instruction (execution := model) (additionSumOp scratch)]

/-- Native widening and sum are followed by actual loaded-modulus reduction. -/
def additionBody (spec : ModulusSpec width) (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (Circuit.forRange 3 (additionStage left right scratch))
    (reduceIntoWord spec (.first (Modular.Reduce.Native.reductionRead scratch.sum)) output)

/-- Allocate exactly the original three arithmetic cells around their actual native program. -/
def addIntoWord (spec : ModulusSpec width) (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (additionShapes width) fun cells _ transport _ =>
    additionBody spec (transport.liftInput left) (transport.liftInput right)
      (additionScratch cells) (transport.liftWrite output)

/-- Real chronological record of each original arithmetic operation. -/
def additionStageRecord (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (index : Fin 3) :
    Store ctx → Store ctx × (additionStage (model := model) left right scratch index).Path := by
  refine Fin.cases (BitWord.instructionStep (execution := model) (additionLeftOp left scratch))
    (fun index => ?_) index
  refine Fin.cases (BitWord.instructionStep (execution := model) (additionRightOp right scratch))
    (fun index => ?_) index
  refine Fin.cases (BitWord.instructionStep (execution := model) (additionSumOp scratch))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- Every original arithmetic operation retains the complete quantum-reference matrix block. -/
lemma additionStage_execute (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (index : Fin 3) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (additionStage (model := model) left right scratch index).execute environment Reference state =
      state.mapClassical
      (fun entry => ((additionStageRecord left right scratch index entry.1).1,
        (entry.2.1, (entry.2.2,
          (additionStageRecord left right scratch index entry.1).2)))) := by
  fin_cases index <;>
    exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model) _
      state

/-- The actual arithmetic and loaded reduction share their true intermediate store. -/
def additionBodyStep (spec : ModulusSpec width) (left right : CInputRef ctx (.unsignedWord width))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (additionBody (model := model) spec left right scratch output).Path :=
  Circuit.sequenceStoreRecord
    (Circuit.forRange 3 (additionStage (model := model) left right scratch))
    (reduceIntoWord spec (.first (Modular.Reduce.Native.reductionRead scratch.sum)) output)
    (Circuit.forRangeStoreRecord 3 (additionStage (model := model) left right scratch)
      (additionStageRecord left right scratch))
    (reduceIntoWordStep spec (.first (Modular.Reduce.Native.reductionRead scratch.sum)) output)

/-- Widening, actual addition and actual loaded reduction compose on the complete state. -/
lemma additionBody_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : AddScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (additionBody (model := model) spec left right scratch output).execute environment Reference
      state =
      state.mapClassical
      (fun entry => ((additionBodyStep spec left right scratch output entry.1).1,
        (entry.2.1, (entry.2.2,
          (additionBodyStep spec left right scratch output entry.1).2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) 3
      (additionStage (model := model) left right scratch)
      (additionStageRecord left right scratch) (additionStage_execute left right scratch))
    (reduceIntoWord_execute _ _ _) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
