/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Pivot

/-!
# Actual GF(2) free-column and nonzero decisions

The original uniqueness test decrements and masks the free-column word,
then performs both original equality tests and stored-bit failure branches.
Every failure executes the original copy marker followed by self-XOR.
Both decisions allocate a word and then a bit, including the original unused
word in the candidate nonzero check. No initial latch value is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The original real copy marker precedes the real stable clear. -/
def markFailure (success : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (pivotRejectedOp success))
    (BitWord.instruction (execution := model) (pivotClearOp success))

/-- The actual stored equality bit selects the original failure arm. -/
def decisionChoice (reject : Bool) (success : CWriteRef ctx .bit) :
    CShape.Value .bit → Circuit model ctx ctx
  | .bit value =>
      match reject, value with
      | false, false => markFailure (model := model) success
      | false, true => .id ctx
      | true, false => .id ctx
      | true, true => markFailure (model := model) success

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The original decrement writes the actual temporary word. -/
def decisionDecrementOp (input output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .decrement width ctx (.storage input.toCStorageRef) output

/-- The actual free word is ANDed with its current decremented word. -/
def decisionMaskOp (input work : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .bitAnd width ctx
    (.product (.storage input.toCStorageRef) (.storage work.toCStorageRef)) work

/-- The real equality instruction writes the actual branch latch. -/
def decisionEqualityOp (left right : CWriteRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx
    (.product (.storage left.toCStorageRef) (.storage right.toCStorageRef)) flag

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- One original equality instruction is immediately followed by its actual stored-bit branch. -/
def decisionTest (reject : Bool) (left right : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (decisionEqualityOp left right flag))
    (.branch (.storage flag.toCStorageRef) (decisionChoice (model := model) reject success))

/-- All original uniqueness instructions execute in their original chronological order. -/
def uniqueFreeBody (free zero work : CWriteRef ctx (.unsignedWord width))
    (success flag : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (decisionDecrementOp free work))
    (.seq (BitWord.instruction (execution := model) (decisionMaskOp free work))
      (.seq (decisionTest (model := model) false work zero success flag)
        (decisionTest (model := model) true free zero success flag)))

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The decision flag follows the original real word allocation. -/
@[reducible] def decisionContext (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  pivotSinkContext (pivotMaskContext ctx width)

/-- Caller destinations retain their original keys through both real decision cells. -/
def decisionWrite (width : Nat) {shape : CShape} (output : CWriteRef ctx shape) :
    CWriteRef (decisionContext ctx width) shape :=
  (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (pivotMaskContext ctx width).canonicalFreshKey
      .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh

/-- The real temporary word remains live below the decision flag. -/
def decisionWork (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (decisionContext ctx width) (.unsignedWord width) :=
  (pivotMaskCell ctx width).underWorkspace (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The original unique-free test runs on the actual lifted inputs and fresh cells. -/
def placedUniqueFree (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) :
    Circuit model (decisionContext ctx width) (decisionContext ctx width) :=
  uniqueFreeBody (model := model) (decisionWrite width free) (decisionWrite width zero)
    (decisionWork ctx width) (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))

/-- The real equality latch is released before the original temporary word. -/
def scopedUniqueFree (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) :
    Circuit model (pivotMaskContext ctx width) (pivotMaskContext ctx width) :=
  .workspace (pivotMaskContext ctx width) (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
      (placedUniqueFree (model := model) free zero success)

/-- The original complete unique-free decision retains its ordered word and bit scopes. -/
def selectUniqueFree (free zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (scopedUniqueFree (model := model) free zero success)

/-- The original candidate check reads the real candidate and zero source below both cells. -/
def placedCandidateNonzero (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) :
    Circuit model (decisionContext ctx width) (decisionContext ctx width) :=
  decisionTest (model := model) true (decisionWrite width candidate) (decisionWrite width zero)
    (decisionWrite width success) (pivotLatch (pivotMaskContext ctx width))

/-- The original nonzero check releases its actual equality flag first. -/
def scopedCandidateNonzero (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) :
    Circuit model (pivotMaskContext ctx width) (pivotMaskContext ctx width) :=
  .workspace (pivotMaskContext ctx width) (pivotMaskContext ctx width).canonicalFreshKey
    .bit (pivotMaskContext ctx width).canonicalFreshKey_fresh
      (placedCandidateNonzero (model := model) candidate zero success)

/-- The original nonzero check keeps its word allocation even though the body never reads it. -/
def checkCandidateNonzero (candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (scopedCandidateNonzero (model := model) candidate zero success)

end

end QuantumAlg.ClassicalRoutines.GF2.Native
