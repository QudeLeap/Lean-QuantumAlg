/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Sub

/-!
# Actual field subtraction with one existing shared modulus

Two lossless widenings, left-plus-modulus and subtract-with-borrow precede
the real quotient/remainder reduction. The same caller modulus is read in
both places. Only four arithmetic temporary cells are allocated; no modulus
is reloaded. The canonical-right condition belongs to the arithmetic proof.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Four original arithmetic temporaries, excluding the already-live shared modulus. -/
def subShapes (width : Nat) : List CShape :=
  [.product (.unsignedWord (width + 1)) .bit, .product (.unsignedWord (width + 1)) .bit,
    .unsignedWord (width + 1), .unsignedWord (width + 1)]

/-- The arithmetic operations retain the actual modulus cell supplied by the caller. -/
def subScratch (cells : Cells ctx (subShapes width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1))) : SubScratch ctx width :=
  ⟨cells.tail.tail.tail.head.ref, cells.tail.tail.head.ref, modulus,
    cells.tail.head.ref, cells.head.ref⟩

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Both operands are snapshotted before the widened augmented subtraction. -/
def subStage (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) : Fin 4 → Circuit model ctx ctx :=
  ![BitWord.instruction (execution := model) (subtractionLeftOp left scratch),
    BitWord.instruction (execution := model) (subtractionRightOp right scratch),
    BitWord.instruction (execution := model) (subtractionAugmentOp scratch),
    BitWord.instruction (execution := model) (subtractionDifferenceOp scratch)]

/-- The same stored modulus supplies both augmentation and the actual final reduction. -/
def subBody (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (Circuit.forRange 4 (subStage left right scratch))
    (reduceWord (.first (reductionRead scratch.difference)) (reductionRead scratch.modulus) output)

/-- Every arithmetic leaf records its actual computed output and chronological Store. -/
def subStageRecord (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (index : Fin 4) :
    Store ctx → Store ctx × (subStage (model := model) left right scratch index).Path := by
  refine Fin.cases (BitWord.instructionStep (execution := model)
    (subtractionLeftOp left scratch)) (fun index => ?_) index
  refine Fin.cases (BitWord.instructionStep (execution := model)
    (subtractionRightOp right scratch)) (fun index => ?_) index
  refine Fin.cases (BitWord.instructionStep (execution := model)
    (subtractionAugmentOp scratch)) (fun index => ?_) index
  refine Fin.cases (BitWord.instructionStep (execution := model)
    (subtractionDifferenceOp scratch)) (fun index => ?_) index
  exact Fin.elim0 index

/-- Every arithmetic leaf preserves the complete original quantum-reference blocks. -/
lemma subStage_execute (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (index : Fin 4) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (subStage (model := model) left right scratch index).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := subStageRecord left right scratch index entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  fin_cases index <;>
    exact BitWord.bitWord_instruction_execute (environment := environment) (execution := model) _
      state

/-- The reduction reads the true arithmetic output and the unchanged shared modulus. -/
def subBodyStep (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (subBody (model := model) left right scratch output).Path :=
  Circuit.sequenceStoreRecord (Circuit.forRange 4 (subStage left right scratch))
    (reduceWord (.first (reductionRead scratch.difference)) (reductionRead scratch.modulus) output)
    (Circuit.forRangeStoreRecord 4 (subStage left right scratch)
      (subStageRecord left right scratch))
    (reduceWordStep (.first (reductionRead scratch.difference)) (reductionRead scratch.modulus)
      output)

/-- The complete six-operation body preserves prior histories and arbitrary Reference. -/
lemma subBody_execute (left right : CInputRef ctx (.unsignedWord width))
    (scratch : SubScratch ctx width) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (subBody (model := model) left right scratch output).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := subBodyStep left right scratch output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) 4
      (subStage (model := model) left right scratch) (subStageRecord left right scratch)
      (subStage_execute left right scratch)) (reduceWord_execute _ _ _) Reference state

/-- Allocate and release only arithmetic scratch around the unchanged existing modulus. -/
def subIntoWord (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (subShapes width) fun cells _ transport _ =>
    subBody (transport.liftInput left) (transport.liftInput right)
      (subScratch cells (transport.liftWrite modulus)) (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
