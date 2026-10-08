/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Workspace
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Actual native modular-negation branch for raw Fourier recovery

A real equality instruction tests the original right-frequency word against
a fresh zero word. Its stored flag selects either a native zero copy or the
original narrowed-modulus subtraction. Both scratch cells remain live until
the actual branch finishes and are then released in reverse allocation order.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- First actual scratch head stores the canonical zero word. -/
@[reducible] def negateZeroCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Second actual scratch head stores the equality result used by the branch. -/
@[reducible] def negateCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  (negateZeroCtx ctx width).addWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- Structural read of an actual writable cell. -/
def negateRead {shape : CShape} (cell : CWriteRef ctx shape) : CInputRef ctx shape :=
  .storage cell.toCStorageRef

/-- Original structural reads retain their exact identities under both scratch scopes. -/
def underNegate {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (negateCtx ctx width) shape :=
  (input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- The output remains the same existing cell under both actual scopes. -/
def writeUnderNegate {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (negateCtx ctx width) shape :=
  (output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- The original zero head stays live through the later flag allocation. -/
def negateZeroCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (negateCtx ctx width) (.unsignedWord width) :=
  (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).underWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- Actual equality-result head. -/
def negateFlagCell (ctx : RuntimeCtx kind) (width : Nat) : CWriteRef (negateCtx ctx width) .bit :=
  CWriteRef.workspaceHead (negateZeroCtx ctx width) (negateZeroCtx ctx width).canonicalFreshKey .bit
    (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- The original equality instruction reads the right word and actual zero scratch. -/
def negateEqualOp (right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product right zero) flag

/-- The selected zero branch writes through an actual native word copy. -/
def negateCopyOp (zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx zero output

/-- The nonzero branch uses the original wrapping word subtraction. -/
def negateSubtractOp (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx (.product modulus right) output

/-- A stored bit selects one of the two original native instructions. -/
def negateChoice {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit) :
    Circuit model ctx ctx :=
  if value.toBool then BitWord.instruction (execution := model) (negateCopyOp zero output)
    else BitWord.instruction (execution := model) (negateSubtractOp modulus right output)

/-- Exact actual selected operation store and its one-instruction path. -/
def negateChoiceStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (store : Store ctx) :
    Store ctx × (negateChoice (model := model) modulus right zero output value).Path :=
  match value with
  | .bit false => BitWord.instructionStep (execution := model)
      (negateSubtractOp modulus right output) store
  | .bit true => BitWord.instructionStep (execution := model) (negateCopyOp zero output) store

/-- Actual equality followed by a structural read of the newly written flag. -/
def negateBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (negateEqualOp right zero flag))
    (.branch (negateRead flag) (negateChoice (model := model) modulus right zero output))

/-- Actual checked store, selected classical value and selected native instruction path. -/
def negateBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right zero : CInputRef ctx (.unsignedWord width))
    (flag : CWriteRef ctx .bit) (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (negateBody (model := model) modulus right zero flag output).Path :=
  let checked := BitWord.instructionStep (execution := model) (negateEqualOp right zero flag) store
  let choice := checked.1.read (negateRead flag)
  let selected := negateChoiceStep (model := model) modulus right zero output choice checked.1
  (selected.1, (checked.2, ⟨choice, selected.2⟩))

/-- The actual inner body uses the two fresh scratch cells and original caller references. -/
def negatePlaced {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (negateCtx ctx width) (negateCtx ctx width) :=
  negateBody (model := model)
    (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width)

/-- The complete original branch with both actual scratch allocations and matching releases. -/
def withNegate {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (negateZeroCtx ctx width) (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh
      (negatePlaced (model := model) modulus right output))

/-- Store produced by precisely the two actual lexical entries. -/
def enterNegate (store : Store ctx) (width : Nat) : Store (negateCtx ctx width) :=
  (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh).pushWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh

/-- Release the exact flag and zero heads after the real branch finishes. -/
def leaveNegate (store : Store (negateCtx ctx width)) : Store ctx :=
  Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (Store.popWorkspace (negateZeroCtx ctx width).canonicalFreshKey .bit
      (negateZeroCtx ctx width).canonicalFreshKey_fresh store)

/-- Complete actual outer store and branch path of the scoped negation. -/
def withNegateStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (modulus right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (withNegate (model := model) modulus right output).Path :=
  let result := negateBodyStep (model := model)
    (underNegate modulus width) (underNegate right width)
    (negateRead (negateZeroCell ctx width)) (negateFlagCell ctx width)
    (writeUnderNegate output width) (enterNegate store width)
  (leaveNegate result.1, result.2)

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native
