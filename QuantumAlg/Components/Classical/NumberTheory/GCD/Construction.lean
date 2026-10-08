/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Step
import all QuantumAlg.Components.Classical.NumberTheory.GCD.StateLayout
import all QuantumAlg.Util.Classical.NumberTheory.Euclidean

/-!
# Expanded native GCD circuit

The retained result is initialized by its actual allocation. Before the final
copy it supplies the internal zero used by comparisons. Three lexical cells
hold the two Euclidean words and their active bit. Only a selected active arm
allocates the division pair, and every lexical scope releases its exact cell.

The existing linear bit-width fuel determines the public iteration schedule.
An inactive iteration selects identity and emits no classical operation.
The caller supplies arbitrary intrinsically bounded operands, with no zero
workspace requirement and no condition excluding zero-width or zero inputs.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Initialize the two actual state words and compute their stored nonzero condition. -/
def initializationBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (.wordUnary .copy width ctx (.first input) first))
    (.seq (BitWord.instruction (execution := model) (.wordUnary .copy width ctx (.second input)
      second))
      (.seq (BitWord.instruction (execution := model) (testActiveOp first zero active))
        (BitWord.instruction (execution := model) (negateActiveOp active))))

/-- Execute one genuine remainder update within its fresh lexical division pair. -/
def scopedRemainder {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh
    (remainderBody
      (first.underWorkspace ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh)
      (second.underWorkspace ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh)
      (zero.underWorkspace ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh)
      (active.underWorkspace ctx.canonicalFreshKey (operandShape width) ctx.canonicalFreshKey_fresh)
      (CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (operandShape width)
        ctx.canonicalFreshKey_fresh))

/-- The branch reads the actual stored bit and charges only the selected body. -/
def guardedRemainder {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit) :
    Circuit model ctx ctx :=
  .branch (cellRead active) (fun value =>
    if value.toBool then scopedRemainder (model := model) first second zero active else .id ctx)

/-- Initialize, execute the public Euclidean schedule, then copy the final previous word. -/
def scheduledBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (operandShape width))
    (first second : CWriteRef ctx (.unsignedWord width))
    (active : CWriteRef ctx .bit) (result : CWriteRef ctx (.unsignedWord width)) :
    Circuit model ctx ctx :=
  .seq (initializationBody (model := model) input first second (cellRead result) active)
    (.seq (.iterate (ClassicalAlgorithms.NumberTheory.Euclid.gcdFuel width)
      (guardedRemainder (model := model) first second (cellRead result) active))
      (BitWord.instruction (execution := model) (.wordUnary .copy width ctx (cellRead second)
        result)))

/-- Place the state body in its three actual lexical allocation scopes. -/
def lexicalBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (operandShape width))
    (result : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (.workspace (currentCtx ctx width) (currentCtx ctx width).canonicalFreshKey
      (.unsignedWord width) (currentCtx ctx width).canonicalFreshKey_fresh
      (.workspace (previousCtx ctx width) (previousCtx ctx width).canonicalFreshKey
        .bit (previousCtx ctx width).canonicalFreshKey_fresh
        (scheduledBody (model := model) (underLoop input width) (currentCell ctx width)
          (previousCell ctx width)
          (conditionCell ctx width) (writeUnderLoop result width))))

/-- Actual final live context, retaining the result beside every original entry. -/
def retainedCtx (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) : RuntimeCtx kind :=
  ctx.addRetained key (.unsignedWord width) fresh

/-- Read the retained result without hiding any other final live cell. -/
def retainedRead (ctx : RuntimeCtx kind) (width : Nat)
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    CInputRef (retainedCtx ctx width key fresh) (.unsignedWord width) :=
  .storage (CStorageRef.retainedHead ctx key (.unsignedWord width) fresh)

/-- Allocate the actual initialized result and run the expanded total GCD algorithm. -/
def retainedCircuit {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (input : CInputRef ctx (operandShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    Circuit model ctx (retainedCtx ctx width key fresh) :=
  .seq (.retain ctx key (.unsignedWord width) fresh)
    (lexicalBody (model := model) (input.underRetained key (.unsignedWord width) fresh)
      (CWriteRef.retainedHead ctx key (.unsignedWord width) fresh))

/-- The selected active body emits precisely the five literal native operations. -/
theorem gcdScopedRemainder_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (scopedRemainder (model := model) first second zero active).Path) :
    (scopedRemainder (model := model) first second zero active).eventTrace path =
      remainderEvents model width := by
  exact gcdRemainder_eventTrace _ _ _ _ _ path

/-- An inactive actual branch has no padding operations in its event trace. -/
theorem gcdGuardedRemainder_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (path : (guardedRemainder (model := model) first second zero active).Path) :
    (guardedRemainder (model := model) first second zero active).eventTrace path =
      if path.1.toBool then remainderEvents model width else [] := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · rfl
      · exact gcdScopedRemainder_eventTrace first second zero active path

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
