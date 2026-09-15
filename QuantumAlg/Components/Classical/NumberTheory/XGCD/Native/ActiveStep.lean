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
def activeBody (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (GCD.divisionOp (firstCell cells) (secondCell cells)
    (activeDivisionCell scratch)))
    (.seq (.classical (activeResizeQuotientOp scratch))
      (.seq (coefficientUpdateBody (coefficientRead (activeQuotientCell scratch))
        (firstLeftCell cells) (secondLeftCell cells)
        (activeProductCell scratch) (activeUpdatedCell scratch))
        (.seq (coefficientUpdateBody (coefficientRead (activeQuotientCell scratch))
          (firstRightCell cells) (secondRightCell cells)
          (activeProductCell scratch) (activeUpdatedCell scratch))
          (.seq (.classical (GCD.rotateSecondOp (firstCell cells) (secondCell cells)))
            (.seq (.classical (GCD.takeRemainderOp (firstCell cells) (activeDivisionCell scratch)))
              (.seq (.classical (GCD.testActiveOp (firstCell cells) zero (activeCell cells)))
                (.classical (GCD.negateActiveOp (activeCell cells)))))))))

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

/-- The concrete finite path of the literal active instruction sequence. -/
def activeBodyPath (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : (activeBody cells scratch zero).Path :=
  ((), ((), (((), ((), ((), ()))), (((), ((), ((), ()))), ((), ((), ((), ())))))))

/-- All fourteen operations retain every quantum-reference block and the actual execution path. -/
theorem xgcdNativeActiveBody_execute (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (activeBody cells scratch zero).execute Reference state =
      state.mapClassical (fun entry =>
        (activeBodyStore cells scratch zero entry.1,
          (entry.2, activeBodyPath cells scratch zero))) := by
  simp only [activeBody, coefficientUpdateBody, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Independent original operation order for one genuinely active Euclidean step. -/
def activeEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.divRem width width),
    .classicalOperation (.wordResize width (PureXGCD.executionCoefficientWidth width))] ++
    coefficientUpdateEvents kind (PureXGCD.executionCoefficientWidth width) ++
    coefficientUpdateEvents kind (PureXGCD.executionCoefficientWidth width) ++
    [.classicalOperation (.wordUnary .copy width),
      .classicalOperation (.wordUnary .copy width),
      .classicalOperation (.wordBinary .equal width), .classicalOperation (.bit .not)]

/-- Every actual body path emits the unchanged native fourteen-operation sequence. -/
theorem xgcdNativeActiveBody_eventTrace (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).eventTrace path = activeEvents kind width := rfl

/-- Native accounting follows the same actual body and its chronological operations. -/
theorem xgcdNativeActiveBody_resourcePool (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).resourcePool path =
      ResourcePool.ofList (activeEvents kind width) := rfl

/-- The dependent native instructions have exact unit-duration depth fourteen. -/
theorem xgcdNativeActiveBody_unitDepth (cells : Cells ctx (stateShapes width))
    (scratch : Cells ctx (activeScratchShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (path : (activeBody cells scratch zero).Path) :
    (activeBody cells scratch zero).depth (fun _ => 1) path = 14 := rfl

/-- Only the selected active arm allocates the four original scratch cells. -/
def scopedActive (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  withCells ctx (activeScratchShapes width) fun scratch _ transport _ =>
    activeBody (transportCells transport cells) scratch (transport.liftInput zero)

/-- The real stored activity bit selects execution; the inactive body is literal identity. -/
def guardedActive (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .branch (GCD.cellRead (activeCell cells)) fun value =>
    if value.toBool then scopedActive cells zero else .id ctx

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
