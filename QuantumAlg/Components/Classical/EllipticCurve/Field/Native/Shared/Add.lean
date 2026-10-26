/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Add

/-!
# Actual field addition with one existing shared modulus

The caller supplies an actual stored modulus. The original two operand
widenings and add-with-carry precede the actual quotient/remainder and resize.
The modulus is read from storage; this component does not materialize it
again. Fresh arithmetic and division cells are released after each call.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared

open Execution ClassicalWorkspace Modular.Reduce.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Widen both original operands, add, and reduce using the same real modulus word. -/
def addBody (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (Circuit.forRange 3 (additionStage left right scratch))
    (reduceWord (.first (reductionRead scratch.sum)) modulus output)

/-- Exact chronological Store and path of the five paid native instructions. -/
def addBodyStep (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width)) :
    Store ctx → Store ctx × (addBody (model := model) left right modulus scratch output).Path :=
  Circuit.sequenceStoreRecord
    (Circuit.forRange 3 (additionStage (model := model) left right scratch))
    (reduceWord (.first (reductionRead scratch.sum)) modulus output)
    (Circuit.forRangeStoreRecord 3 (additionStage (model := model) left right scratch)
      (additionStageRecord left right scratch))
    (reduceWordStep (.first (reductionRead scratch.sum)) modulus output)

/-- Complete joint quantum-reference blocks and all prior histories follow that actual record. -/
lemma addBody_execute (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (scratch : AddScratch ctx width) (output : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (addBody (model := model) left right modulus scratch output).execute environment
      Reference state = state.mapClassical (fun entry =>
        let result := addBodyStep left right modulus scratch output entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  exact Circuit.execute_sequenceStoreRecord (environment := environment) (model := model) _ _ _ _
    (Circuit.execute_forRangeStoreRecord (environment := environment) (model := model) 3
      (additionStage (model := model) left right scratch)
      (additionStageRecord left right scratch) (additionStage_execute left right scratch))
    (reduceWord_execute _ _ _) Reference state

/-- Allocate only the real temporary arithmetic cells; preserve caller operands and modulus. -/
def addIntoWord (left right : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (width + 1)))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (additionShapes width) fun cells _ transport _ =>
    addBody (transport.liftInput left) (transport.liftInput right)
      (transport.liftInput modulus) (additionScratch cells) (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native.Shared
