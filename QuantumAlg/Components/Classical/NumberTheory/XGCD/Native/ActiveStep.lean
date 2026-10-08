/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.StateLayout
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Step
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Transport

/-!
# One actual extended-Euclidean active step

The division and resized quotient precede both coefficient updates. Only then
are the remainder words rotated and the activity bit refreshed. This is the
original fourteen-operation order, at the original execution coefficient
width. Four lexical scratch cells retain the division pair, quotient, product
and updated coefficient; the two coefficient updates reuse the latter pair.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original division pair and three execution-width scratch words. -/
def activeScratchShapes (width : Nat) : List CShape :=
  [.product (.unsignedWord width) (.unsignedWord width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width),
    .unsignedWord (PureXGCD.executionCoefficientWidth width)]

/-- Both ordinary-width division outputs occupy one actual product cell. -/
def activeDivisionCell (scratch : Cells ctx (activeScratchShapes width)) :
    CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)) :=
  (cellAt scratch ⟨0, by change 0 < 4; decide⟩).ref

/-- The resized quotient is retained throughout both coefficient updates. -/
def activeQuotientCell (scratch : Cells ctx (activeScratchShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt scratch ⟨1, by change 1 < 4; decide⟩).ref

/-- Shared low-product scratch for the left and right coefficient recurrences. -/
def activeProductCell (scratch : Cells ctx (activeScratchShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt scratch ⟨2, by change 2 < 4; decide⟩).ref

/-- Shared subtraction output, consumed before the next coefficient update. -/
def activeUpdatedCell (scratch : Cells ctx (activeScratchShapes width)) :
    CWriteRef ctx (.unsignedWord (PureXGCD.executionCoefficientWidth width)) :=
  (cellAt scratch ⟨3, by change 3 < 4; decide⟩).ref

/-- Widen the actually computed quotient through its charged native instruction. -/
def activeResizeQuotientOp (scratch : Cells ctx (activeScratchShapes width)) :
    ClassicalOp (.unsignedWord width)
      (.unsignedWord (PureXGCD.executionCoefficientWidth width)) ctx ctx :=
  .wordResize width (PureXGCD.executionCoefficientWidth width) ctx
    (.first (GCD.cellRead (activeDivisionCell scratch))) (activeQuotientCell scratch)

/-- Literal original division, two coefficient updates, remainder rotation and activity refresh. -/
def activeBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (GCD.divisionOp (firstCell cells) (secondCell
    cells)
    (activeDivisionCell scratch)))
    (.seq (BitWord.instruction (execution := model) (activeResizeQuotientOp scratch))
      (.seq (coefficientUpdateBody (model := model) (coefficientRead (activeQuotientCell scratch))
        (firstLeftCell cells) (secondLeftCell cells)
        (activeProductCell scratch) (activeUpdatedCell scratch))
        (.seq (coefficientUpdateBody (model := model) (coefficientRead (activeQuotientCell scratch))
          (firstRightCell cells) (secondRightCell cells)
          (activeProductCell scratch) (activeUpdatedCell scratch))
          (.seq (BitWord.instruction (execution := model) (GCD.rotateSecondOp (firstCell cells)
            (secondCell cells)))
            (.seq (BitWord.instruction (execution := model) (GCD.takeRemainderOp (firstCell
              cells) (activeDivisionCell scratch)))
              (.seq (BitWord.instruction (execution := model) (GCD.testActiveOp (firstCell cells)
                zero (activeCell cells)))
                (BitWord.instruction (execution := model) (GCD.negateActiveOp (activeCell
                  cells)))))))))

/-- The exact sequence of stores includes both updates using the same physical scratch pair. -/
def activeBodyStore (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  let divided := store.applyOp (GCD.divisionOp (firstCell cells) (secondCell cells)
    (activeDivisionCell scratch))
  let widened := divided.applyOp (activeResizeQuotientOp scratch)
  let left := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstLeftCell cells) (secondLeftCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) widened
  let right := coefficientUpdateStore (coefficientRead (activeQuotientCell scratch))
    (firstRightCell cells) (secondRightCell cells)
    (activeProductCell scratch) (activeUpdatedCell scratch) left
  (((right.applyOp (GCD.rotateSecondOp (firstCell cells) (secondCell cells))).applyOp
    (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch))).applyOp
      (GCD.testActiveOp (firstCell cells) zero (activeCell cells))).applyOp
        (GCD.negateActiveOp (activeCell cells))

/-- The actual returned primitive values compose the original fourteen-operation record. -/
def activeBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (activeBody (model := model) cells scratch zero).Path :=
  let divided := BitWord.instructionStep (execution := model)
    (GCD.divisionOp (firstCell cells) (secondCell cells) (activeDivisionCell scratch)) store
  let widened := BitWord.instructionStep (execution := model) (activeResizeQuotientOp scratch)
    divided.1
  let left := coefficientUpdateStep (model := model) (coefficientRead (activeQuotientCell scratch))
    (firstLeftCell cells) (secondLeftCell cells) (activeProductCell scratch)
    (activeUpdatedCell scratch) widened.1
  let right := coefficientUpdateStep (model := model) (coefficientRead (activeQuotientCell scratch))
    (firstRightCell cells) (secondRightCell cells) (activeProductCell scratch)
    (activeUpdatedCell scratch) left.1
  let rotated := BitWord.instructionStep (execution := model)
    (GCD.rotateSecondOp (firstCell cells) (secondCell cells)) right.1
  let taken := BitWord.instructionStep (execution := model)
    (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)) rotated.1
  let tested := BitWord.instructionStep (execution := model)
    (GCD.testActiveOp (firstCell cells) zero (activeCell cells)) taken.1
  let negated := BitWord.instructionStep (execution := model)
    (GCD.negateActiveOp (activeCell cells)) tested.1
  (negated.1, (divided.2, (widened.2, (left.2, (right.2,
    (rotated.2, (taken.2, (tested.2, negated.2))))))))

/-- The path records the actual store-dependent native results. -/
def activeBodyPath {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    (activeBody (model := model) cells scratch zero).Path :=
  (activeBodyStep (model := model) cells scratch zero store).2

/-- All fourteen operations retain every quantum-reference block and the actual execution path. -/
theorem xgcdNativeActiveBody_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (activeBody (model := model) cells scratch zero).execute Reference state =
      state.mapClassical (fun entry =>
        let result := activeBodyStep (model := model) cells scratch zero entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [activeBody, Circuit.execute_seq, xgcdCoefficientUpdate_execute,
    BitWord.bitWord_instruction_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Independent original operation order for one genuinely active Euclidean step. -/
def activeEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.divRem width width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize width
      (PureXGCD.executionCoefficientWidth width)))] ++
    coefficientUpdateEvents model (PureXGCD.executionCoefficientWidth width) ++
    coefficientUpdateEvents model (PureXGCD.executionCoefficientWidth width) ++
    [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy
        width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal
        width)), .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- Every actual body path emits the unchanged native fourteen-operation sequence. -/
theorem xgcdNativeActiveBody_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).eventTrace path = activeEvents model width
      := by
  change (BitWord.instruction (execution := model) (GCD.divisionOp (firstCell cells) (secondCell
    cells) (activeDivisionCell scratch))).eventTrace
    path.1 ++ ((BitWord.instruction (execution := model) (activeResizeQuotientOp
      scratch)).eventTrace
    path.2.1 ++ ((coefficientUpdateBody (model := model) (coefficientRead (activeQuotientCell
      scratch))
      (firstLeftCell cells) (secondLeftCell cells)
      (activeProductCell scratch) (activeUpdatedCell scratch)).eventTrace
    path.2.2.1 ++ ((coefficientUpdateBody (model := model) (coefficientRead (activeQuotientCell
      scratch))
      (firstRightCell cells) (secondRightCell cells)
      (activeProductCell scratch) (activeUpdatedCell scratch)).eventTrace
    path.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.rotateSecondOp (firstCell
      cells) (secondCell cells))).eventTrace
    path.2.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.takeRemainderOp (firstCell
      cells) (activeDivisionCell scratch))).eventTrace
    path.2.2.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.testActiveOp (firstCell
      cells) zero (activeCell cells))).eventTrace
    path.2.2.2.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.negateActiveOp
      (activeCell cells))).eventTrace
    path.2.2.2.2.2.2.2))))))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    xgcdCoefficientUpdate_eventTrace, xgcdCoefficientUpdate_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  simp only [activeEvents, List.cons_append, List.nil_append, List.append_assoc]
  rfl

/-- Native accounting follows the same actual body and its chronological operations. -/
theorem xgcdNativeActiveBody_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).resourcePool path =
      ResourcePool.ofList (activeEvents model width) :=
  congrArg ResourcePool.ofList (xgcdNativeActiveBody_eventTrace cells scratch zero path)

/-- The dependent native instructions have exact unit-duration depth fourteen. -/
theorem xgcdNativeActiveBody_unitDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody (model := model) cells scratch zero).Path) :
    (activeBody (model := model) cells scratch zero).depth (fun _ => 1) path = 14 := rfl

/-- Only the selected active arm allocates the four original scratch cells. -/
def scopedActive {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  withCells ctx (activeScratchShapes width) fun scratch _ transport _ =>
    activeBody (model := model) (transportCells transport cells) scratch (transport.liftInput zero)

/-- The real stored activity bit selects execution; the inactive body is literal identity. -/
def guardedActive {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .branch (GCD.cellRead (activeCell cells)) fun value =>
    if value.toBool then scopedActive (model := model) cells zero else .id ctx

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
