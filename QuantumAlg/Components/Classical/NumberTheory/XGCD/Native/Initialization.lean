/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.StateLayout
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Step
import all QuantumAlg.Core.Execution.Trace

/-!
# Six actual instructions initialize the extended-Euclidean state

Two copies retain the original operand order. Two increments establish the
coefficient basis `(1,0),(0,1)` on the genuinely fresh lexical cells. The
original equality comparison and negation set the activity bit. The zero
sentinel is the enclosing retained result's actual allocation value.

The exact interpreter equation below allows arbitrary prior internal contents;
the separate initialization theorem uses values established by lexical entry.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Copy the original left operand into the current remainder. -/
def copyFirstOp (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width))) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (.first input) (firstCell cells)

/-- Copy the original right operand into the previous remainder. -/
def copySecondOp (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width))) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (.second input) (secondCell cells)

/-- Increment the actually allocated zero left coefficient of the current remainder. -/
def incrementFirstLeftOp (cells : Cells ctx (stateShapes width)) :
    ClassicalOp (.unsignedWord (PureXGCD.executionCoefficientWidth width))
      (.unsignedWord (PureXGCD.executionCoefficientWidth width)) ctx ctx :=
  .wordUnary .increment (PureXGCD.executionCoefficientWidth width) ctx
    (GCD.cellRead (firstLeftCell cells)) (firstLeftCell cells)

/-- Increment the actually allocated zero right coefficient of the previous remainder. -/
def incrementSecondRightOp (cells : Cells ctx (stateShapes width)) :
    ClassicalOp (.unsignedWord (PureXGCD.executionCoefficientWidth width))
      (.unsignedWord (PureXGCD.executionCoefficientWidth width)) ctx ctx :=
  .wordUnary .increment (PureXGCD.executionCoefficientWidth width) ctx
    (GCD.cellRead (secondRightCell cells)) (secondRightCell cells)

/-- The original copy, copy, increment, increment, equality, negation instruction order. -/
def initializationBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (copyFirstOp cells input))
    (.seq (BitWord.instruction (execution := model) (copySecondOp cells input))
      (.seq (BitWord.instruction (execution := model) (incrementFirstLeftOp cells))
        (.seq (BitWord.instruction (execution := model) (incrementSecondRightOp cells))
          (.seq (BitWord.instruction (execution := model) (GCD.testActiveOp (firstCell cells)
            zero (activeCell cells)))
            (BitWord.instruction (execution := model) (GCD.negateActiveOp (activeCell cells)))))))

/-- The actual store after exactly those six closed operations. -/
def initializationStore (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (((((store.applyOp (copyFirstOp cells input)).applyOp (copySecondOp cells input)).applyOp
    (incrementFirstLeftOp cells)).applyOp (incrementSecondRightOp cells)).applyOp
      (GCD.testActiveOp (firstCell cells) zero (activeCell cells))).applyOp
        (GCD.negateActiveOp (activeCell cells))

/-- Actual primitive outputs retain the initialization's complete chronological path. -/
def initializationStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (initializationBody (model := model) cells input zero).Path :=
  let first := BitWord.instructionStep (execution := model) (copyFirstOp cells input)
    store
  let second := BitWord.instructionStep (execution := model) (copySecondOp cells input)
    first.1
  let third := BitWord.instructionStep (execution := model) (incrementFirstLeftOp cells)
    second.1
  let fourth := BitWord.instructionStep (execution := model) (incrementSecondRightOp cells)
    third.1
  let fifth := BitWord.instructionStep (execution := model) (GCD.testActiveOp (firstCell cells)
    zero (activeCell cells))
    fourth.1
  let sixth := BitWord.instructionStep (execution := model) (GCD.negateActiveOp (activeCell cells))
    fifth.1
  (sixth.1, (first.2, (second.2, (third.2, (fourth.2, (fifth.2, sixth.2))))))

/-- All original quantum-reference blocks and the complete six-step path are retained. -/
theorem xgcdNativeInitialization_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (initializationBody (model := model) cells input zero).execute Reference state =
      state.mapClassical (fun entry =>
        let result := initializationStep (model := model) cells input zero entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [initializationBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Independent original six-operation initialization trace at the original widths. -/
def initializationEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .increment
      (PureXGCD.executionCoefficientWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .increment
      (PureXGCD.executionCoefficientWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal
      width)), .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))]

/-- Every actual initialization path emits precisely the original six native operations. -/
theorem xgcdNativeInitialization_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody (model := model) cells input zero).Path) :
    (initializationBody (model := model) cells input zero).eventTrace path = initializationEvents
      model width := by
  change (BitWord.instruction (execution := model) (copyFirstOp cells input)).eventTrace
    path.1 ++ ((BitWord.instruction (execution := model) (copySecondOp cells input)).eventTrace
    path.2.1 ++ ((BitWord.instruction (execution := model) (incrementFirstLeftOp cells)).eventTrace
    path.2.2.1 ++ ((BitWord.instruction (execution := model) (incrementSecondRightOp
      cells)).eventTrace
    path.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.testActiveOp (firstCell
      cells) zero (activeCell cells))).eventTrace
    path.2.2.2.2.1 ++ ((BitWord.instruction (execution := model) (GCD.negateActiveOp (activeCell
      cells))).eventTrace
    path.2.2.2.2.2))))) = _
  rw [BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Resource accounting follows those same actual initialization operations. -/
theorem xgcdNativeInitialization_resourcePool {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody (model := model) cells input zero).Path) :
    (initializationBody (model := model) cells input zero).resourcePool path =
      ResourcePool.ofList (initializationEvents model width) :=
  congrArg ResourcePool.ofList (xgcdNativeInitialization_eventTrace cells input zero path)

/-- The six actual dependent operations contribute six units of serial depth. -/
theorem xgcdNativeInitialization_unitDepth {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody (model := model) cells input zero).Path) :
    (initializationBody (model := model) cells input zero).depth (fun _ => 1) path = 6 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
