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
def initializationBody (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (copyFirstOp cells input))
    (.seq (.classical (copySecondOp cells input))
      (.seq (.classical (incrementFirstLeftOp cells))
        (.seq (.classical (incrementSecondRightOp cells))
          (.seq (.classical (GCD.testActiveOp (firstCell cells) zero (activeCell cells)))
            (.classical (GCD.negateActiveOp (activeCell cells)))))))

/-- The actual store after exactly those six closed operations. -/
def initializationStore (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  (((((store.applyOp (copyFirstOp cells input)).applyOp (copySecondOp cells input)).applyOp
    (incrementFirstLeftOp cells)).applyOp (incrementSecondRightOp cells)).applyOp
      (GCD.testActiveOp (firstCell cells) zero (activeCell cells))).applyOp
        (GCD.negateActiveOp (activeCell cells))

/-- All original quantum-reference blocks and the complete six-step path are retained. -/
theorem xgcdNativeInitialization_execute (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (initializationBody cells input zero).execute Reference state =
      state.mapClassical (fun entry =>
        (initializationStore cells input zero entry.1,
          (entry.2, ((), ((), ((), ((), ((), ())))))))) := by
  simp only [initializationBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1

/-- Independent original six-operation initialization trace at the original widths. -/
def initializationEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .copy width),
    .classicalOperation (.wordUnary .increment (PureXGCD.executionCoefficientWidth width)),
    .classicalOperation (.wordUnary .increment (PureXGCD.executionCoefficientWidth width)),
    .classicalOperation (.wordBinary .equal width), .classicalOperation (.bit .not)]

/-- Every actual initialization path emits precisely the original six native operations. -/
theorem xgcdNativeInitialization_eventTrace (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).eventTrace path = initializationEvents kind width := rfl

/-- Resource accounting follows those same actual initialization operations. -/
theorem xgcdNativeInitialization_resourcePool (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).resourcePool path =
      ResourcePool.ofList (initializationEvents kind width) := rfl

/-- The six actual dependent operations contribute six units of serial depth. -/
theorem xgcdNativeInitialization_unitDepth (cells : Cells ctx (stateShapes width))
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (initializationBody cells input zero).Path) :
    (initializationBody cells input zero).depth (fun _ => 1) path = 6 := rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
