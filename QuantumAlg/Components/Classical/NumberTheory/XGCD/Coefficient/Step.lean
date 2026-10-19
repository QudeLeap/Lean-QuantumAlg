/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.Classical.Model.BitWord.Execution

/-!
# Native extended-Euclidean coefficient rotation

The four actual instructions compute the low product, subtract it from the
previous coefficient, and rotate the two coefficient words. Arithmetic uses
the supplied execution width. The signed interpretation and its range proof
are separate from this exact circuit and store equation.

Every quantum block, including its external reference, is retained by these
classical instructions. Scratch values need no initialization promise.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural read of an actual coefficient or scratch cell. -/
def coefficientRead (cell : CWriteRef ctx (.unsignedWord width)) :
    CInputRef ctx (.unsignedWord width) := .storage cell.toCStorageRef

/-- Compute the quotient times the current coefficient modulo the word size. -/
def coefficientProductOp (quotient : CInputRef ctx (.unsignedWord width))
    (first product : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product quotient (coefficientRead first)) product

/-- Subtract the computed product from the previous coefficient. -/
def coefficientSubtractOp (second product updated : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .sub width ctx
    (.product (coefficientRead second) (coefficientRead product)) updated

/-- Copy one existing coefficient word through a charged native instruction. -/
def coefficientCopyOp (source target : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (coefficientRead source) target

/-- Four literal instructions implement one coefficient recurrence and rotation. -/
def coefficientUpdateBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (coefficientProductOp quotient first product))
    (.seq (BitWord.instruction (execution := model) (coefficientSubtractOp second product updated))
      (.seq (BitWord.instruction (execution := model) (coefficientCopyOp first second))
        (BitWord.instruction (execution := model) (coefficientCopyOp updated first))))

/-- The actual store produced by precisely those four instruction evaluations. -/
def coefficientUpdateStore (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : Store ctx :=
  (((store.applyOp (coefficientProductOp quotient first product)).applyOp
    (coefficientSubtractOp second product updated)).applyOp
      (coefficientCopyOp first second)).applyOp (coefficientCopyOp updated first)

/-- The four native result values form the actual chronological update path. -/
def coefficientUpdateStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (coefficientUpdateBody (model := model) quotient first second product
      updated).Path :=
  let multiplied := BitWord.instructionStep (execution := model)
    (coefficientProductOp quotient first product) store
  let subtracted := BitWord.instructionStep (execution := model)
    (coefficientSubtractOp second product updated) multiplied.1
  let rotated := BitWord.instructionStep (execution := model) (coefficientCopyOp first second)
    subtracted.1
  let copied := BitWord.instructionStep (execution := model) (coefficientCopyOp updated first)
    rotated.1
  (copied.1, (multiplied.2, (subtracted.2, (rotated.2, copied.2))))

/-- The complete execution preserves each quantum-reference block and records its real path. -/
lemma xgcdCoefficientUpdate_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (coefficientUpdateBody (model := model) quotient first second product updated).execute
      environment Reference state =
      state.mapClassical (fun entry =>
        let result := coefficientUpdateStep (model := model) quotient first second product updated
          entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [coefficientUpdateBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Independent operation list for one extended-Euclidean coefficient update. -/
def coefficientUpdateEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
  List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .mulLow
    width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .sub width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width))]

/-- The actual path emits one low product, one subtraction, and two copies. -/
lemma xgcdCoefficientUpdate_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody (model := model) quotient first second product updated).Path) :
    (coefficientUpdateBody (model := model) quotient first second product updated).eventTrace path =
      coefficientUpdateEvents model width := by
  change (BitWord.instruction (execution := model)
    (coefficientProductOp quotient first product)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (coefficientSubtractOp second product updated)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (coefficientCopyOp first second)).eventTrace
        path.2.2.1 ++ (BitWord.instruction (execution := model)
          (coefficientCopyOp updated first)).eventTrace path.2.2.2)) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The native resource pool is derived from these same four instructions. -/
lemma xgcdCoefficientUpdate_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody (model := model) quotient first second product updated).Path) :
    (coefficientUpdateBody (model := model) quotient first second product updated).resourcePool
      path =
      ResourcePool.ofList (coefficientUpdateEvents model width) :=
  congrArg ResourcePool.ofList
    (xgcdCoefficientUpdate_eventTrace quotient first second product updated path)

/-- All four dependent operations contribute unit-duration serial depth. -/
lemma xgcdCoefficientUpdate_unitDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (path : (coefficientUpdateBody (model := model) quotient first second product updated).Path) :
    (coefficientUpdateBody (model := model) quotient first second product updated).depth (fun _
      => 1) path = 4 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
