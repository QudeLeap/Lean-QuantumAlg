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
# Actual original raw field subtraction

The original five lexical cells retain widened operands, the first loaded
modulus and both flagged arithmetic results. After widening and loading, the
native operations compute left plus modulus and subtract right. The original
reduction then allocates and loads its own modulus a second time.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular
open Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The five original raw subtraction cells, retaining both arithmetic flag bits. -/
structure SubScratch (ctx : RuntimeCtx kind) (width : Nat) where
  left : CWriteRef ctx (.unsignedWord (width + 1))
  right : CWriteRef ctx (.unsignedWord (width + 1))
  modulus : CWriteRef ctx (.unsignedWord (width + 1))
  augmented : CWriteRef ctx (.product (.unsignedWord (width + 1)) .bit)
  difference : CWriteRef ctx (.product (.unsignedWord (width + 1)) .bit)

/-- Deepest-first cells preserve the original left/right/modulus/augmented/difference allocation. -/
def subtractionShapes (width : Nat) : List CShape :=
  [.product (.unsignedWord (width + 1)) .bit, .product (.unsignedWord (width + 1)) .bit,
    .unsignedWord (width + 1), .unsignedWord (width + 1), .unsignedWord (width + 1)]

/-- Each actual allocated cell retains its original arithmetic role. -/
def subtractionScratch (cells : Cells ctx (subtractionShapes width)) : SubScratch ctx width :=
  ⟨cells.tail.tail.tail.tail.head.ref, cells.tail.tail.tail.head.ref,
    cells.tail.tail.head.ref, cells.tail.head.ref, cells.head.ref⟩

/-- Original one-bit widening of the actual left operand. -/
def subtractionLeftOp (left : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx left scratch.left

/-- Original one-bit widening of the actual right operand. -/
def subtractionRightOp (right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + 1)) ctx ctx :=
  .wordResize width (width + 1) ctx right scratch.right

/-- Actual addition of the widened left operand and the first materialized modulus. -/
def subtractionAugmentOp (scratch : SubScratch ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.product (.unsignedWord (width + 1)) .bit) ctx ctx :=
  .addCarry (width + 1) ctx
    (.product (reductionRead scratch.left) (reductionRead scratch.modulus)) scratch.augmented

/-- Original actual subtraction retains both the low word and the borrow flag. -/
def subtractionDifferenceOp (scratch : SubScratch ctx width) :
    ClassicalOp (.product (.unsignedWord (width + 1)) (.unsignedWord (width + 1)))
      (.product (.unsignedWord (width + 1)) .bit) ctx ctx :=
  .subBorrow (width + 1) ctx
    (.product (.first (reductionRead scratch.augmented))
      (reductionRead scratch.right)) scratch.difference

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual modulus loading occurs between both widenings and both arithmetic operations. -/
def subtractionStage (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width) :
    Fin 5 → Circuit model ctx ctx :=
  ![BitWord.instruction (execution := model) (subtractionLeftOp left scratch),
    BitWord.instruction (execution := model) (subtractionRightOp right scratch),
    ConstantWord.circuit scratch.modulus spec.modulus,
    BitWord.instruction (execution := model) (subtractionAugmentOp scratch),
    BitWord.instruction (execution := model) (subtractionDifferenceOp scratch)]

/-- A separately loaded reduction follows the complete original subtraction prefix. -/
def subtractionBody (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (Circuit.forRange 5 (subtractionStage spec left right scratch))
    (reduceIntoWord spec (.first (reductionRead scratch.difference)) output)

/-- Actual allocation and release surround the original complete raw subtraction instructions. -/
def subIntoWord (spec : ModulusSpec width) (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (subtractionShapes width) fun cells _ transport _ =>
    subtractionBody spec (transport.liftInput left) (transport.liftInput right)
      (subtractionScratch cells) (transport.liftWrite output)

/-- Every stage returns its actual complete store and its actual instruction path. -/
def subtractionStageRecord (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (index : Fin 5) :
    Store ctx → Store ctx ×
      (subtractionStage (model := model) spec left right scratch index).Path := by
  refine Fin.cases
    (BitWord.instructionStep (execution := model) (subtractionLeftOp left scratch))
    (fun index => ?_) index
  refine Fin.cases
    (BitWord.instructionStep (execution := model) (subtractionRightOp right scratch))
    (fun index => ?_) index
  refine Fin.cases (ConstantWord.foldStep scratch.modulus
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))) (fun index => ?_) index
  refine Fin.cases
    (BitWord.instructionStep (execution := model) (subtractionAugmentOp scratch))
    (fun index => ?_) index
  refine Fin.cases
    (BitWord.instructionStep (execution := model) (subtractionDifferenceOp scratch))
    (fun index => ?_) index
  exact Fin.elim0 index

/-- The actual native stages and real first modulus loader retain full reference correlations. -/
theorem subtractionStage_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (index : Fin 5) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (subtractionStage (model := model) spec left right scratch index).execute Reference state =
      state.mapClassical
      (fun entry => ((subtractionStageRecord spec left right scratch index entry.1).1,
        (entry.2.1, (entry.2.2,
          (subtractionStageRecord spec left right scratch index entry.1).2)))) := by
  fin_cases index
  all_goals first
    | exact ConstantWord.constantWord_fold_execute scratch.modulus _ Reference state
    | exact BitWord.bitWord_instruction_execute (execution := model) _ state

/-- The true arithmetic and separately loaded reduction share their actual intermediate store. -/
def subtractionBodyStep (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx ×
      (subtractionBody (model := model) spec left right scratch output).Path :=
  Circuit.sequenceStoreRecord
    (Circuit.forRange 5 (subtractionStage (model := model) spec left right scratch))
    (reduceIntoWord spec (.first (reductionRead scratch.difference)) output)
    (Circuit.forRangeStoreRecord 5 (subtractionStage (model := model) spec left right scratch)
      (subtractionStageRecord spec left right scratch))
    (reduceIntoWordStep spec (.first (reductionRead scratch.difference)) output)

/-- Both actual modulus loads and the original arithmetic compose on the complete state. -/
theorem subtractionBody_execute (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width)) (scratch : SubScratch ctx width)
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (subtractionBody (model := model) spec left right scratch output).execute Reference state =
      state.mapClassical
      (fun entry => ((subtractionBodyStep spec left right scratch output entry.1).1,
        (entry.2.1, (entry.2.2,
          (subtractionBodyStep spec left right scratch output entry.1).2)))) := by
  exact Circuit.execute_sequenceStoreRecord (model := model) _ _ _ _
    (Circuit.execute_forRangeStoreRecord (model := model) 5
      (subtractionStage (model := model) spec left right scratch)
      (subtractionStageRecord spec left right scratch)
      (subtractionStage_execute spec left right scratch))
    (reduceIntoWord_execute _ _ _) Reference state

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
