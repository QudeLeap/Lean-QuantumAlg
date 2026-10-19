/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine
import all QuantumAlg.Components.Classical.NumberTheory.Representation
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# Original five-instruction public XGCD result packing

One shared public-width raw word is reused for the two coefficient resizes.
Each coefficient is packed into its own actual signed cell before the final
right-nested result pack. The original three lexical scratch cells enclose
exactly these five operations; no decoded result is substituted for execution.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original raw narrowing word and two distinct signed coefficient cells. -/
def packingShapes (width : Nat) : List CShape :=
  [.unsignedWord (coefficientWidth width),
    SignedShape (coefficientWidth width), SignedShape (coefficientWidth width)]

/-- The original five actual instructions, including both signed nominal boundaries. -/
def packingBody {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (.wordResize (PureXGCD.executionCoefficientWidth
    width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.leftCoefficient) raw))
    (.seq (BitWord.instruction (execution := model) (.packBoundedSignedWord (coefficientWidth
      width) ctx
      (GCD.cellRead raw) left))
      (.seq (BitWord.instruction (execution := model) (.wordResize
        (PureXGCD.executionCoefficientWidth width)
        (coefficientWidth width) ctx (GCD.cellRead outputs.rightCoefficient) raw))
        (.seq (BitWord.instruction (execution := model) (.packBoundedSignedWord (coefficientWidth
          width) ctx
          (GCD.cellRead raw) right))
          (BitWord.instruction (execution := model) (.packProduct ctx
            (.product (GCD.cellRead outputs.gcd)
              (.product (GCD.cellRead left) (GCD.cellRead right))) result)))))

/-- The literal actual five-operation store transformation. -/
def packingBodyStore (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (store : Store ctx) : Store ctx :=
  ((((store.applyOp (.wordResize (PureXGCD.executionCoefficientWidth width)
    (coefficientWidth width) ctx (GCD.cellRead outputs.leftCoefficient) raw)).applyOp
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) left)).applyOp
      (.wordResize (PureXGCD.executionCoefficientWidth width)
        (coefficientWidth width) ctx (GCD.cellRead outputs.rightCoefficient) raw)).applyOp
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) right)).applyOp
      (.packProduct ctx (.product (GCD.cellRead outputs.gcd)
        (.product (GCD.cellRead left) (GCD.cellRead right))) result)

/-- Actual chronological outputs of the original five packing instructions. -/
def packingBodyStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (before : Store ctx) :
    Store ctx × (packingBody (model := model) outputs raw left right result).Path :=
  let first := BitWord.instructionStep (execution := model)
    (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)
      ctx (GCD.cellRead outputs.leftCoefficient) raw) before
  let second := BitWord.instructionStep (execution := model)
    (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) left) first.1
  let third := BitWord.instructionStep (execution := model)
    (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)
      ctx (GCD.cellRead outputs.rightCoefficient) raw) second.1
  let fourth := BitWord.instructionStep (execution := model)
    (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) right) third.1
  let fifth := BitWord.instructionStep (execution := model)
    (.packProduct ctx (.product (GCD.cellRead outputs.gcd)
      (.product (GCD.cellRead left) (GCD.cellRead right))) result) fourth.1
  (fifth.1, (first.2, (second.2, (third.2, (fourth.2, fifth.2)))))

/-- The actual native result record has the original five-operation store projection. -/
lemma xgcdNativePackingBody_step_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (before : Store ctx) :
    (packingBodyStep (model := model) outputs raw left right result before).1 =
      packingBodyStore outputs raw left right result before := rfl

/-- Every full quantum-reference block retains the actual store and all five instruction paths. -/
lemma xgcdNativePackingBody_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (packingBody (model := model) outputs raw left right result).execute environment
      Reference state =
      state.mapClassical (fun entry =>
        let actual := packingBodyStep (model := model) outputs raw left right result entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [packingBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Allocate the original three packing cells and return the actual public result destination. -/
def packRawOutputs {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (outputs : RawOutputs ctx width)
    (result : CWriteRef ctx (XGCDOutputShape width)) : Circuit model ctx ctx :=
  withCells ctx (packingShapes width) fun cells _ transport _ =>
    packingBody (model := model) (outputs.transport transport) cells.head.ref cells.tail.head.ref
      cells.tail.tail.head.ref (transport.liftWrite result)

/-- The original two resizes, two signed packs and one right-nested product pack. -/
def packingEvents (model : ExecutionModel) [BitWord.Selected model] (width : Nat) : List
  (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize
    (PureXGCD.executionCoefficientWidth width) (coefficientWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.nominalEncoding
      (.packBoundedSignedWord (coefficientWidth width)))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordResize
      (PureXGCD.executionCoefficientWidth width) (coefficientWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.nominalEncoding
      (.packBoundedSignedWord (coefficientWidth width)))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.nominalEncoding
      (.packProduct width (coefficientWidth width + coefficientWidth width))))]

/-- Original actual event list before the scratch scopes are released. -/
lemma xgcdNativePackingBody_eventTrace {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (outputs : RawOutputs ctx width)
    (raw : CWriteRef ctx (.unsignedWord (coefficientWidth width)))
    (left right : CWriteRef ctx (SignedShape (coefficientWidth width)))
    (result : CWriteRef ctx (XGCDOutputShape width))
    (path : (packingBody (model := model) outputs raw left right result).Path) :
    (packingBody (model := model) outputs raw left right result).eventTrace path = packingEvents
      model width := by
  change (BitWord.instruction (execution := model)
    (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)
      ctx (GCD.cellRead outputs.leftCoefficient) raw)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model)
      (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) left)).eventTrace
        path.2.1 ++
      ((BitWord.instruction (execution := model)
        (.wordResize (PureXGCD.executionCoefficientWidth width) (coefficientWidth width)
          ctx (GCD.cellRead outputs.rightCoefficient) raw)).eventTrace path.2.2.1 ++
        ((BitWord.instruction (execution := model)
          (.packBoundedSignedWord (coefficientWidth width) ctx (GCD.cellRead raw) right)).eventTrace
            path.2.2.2.1 ++
          (BitWord.instruction (execution := model)
            (.packProduct ctx (.product (GCD.cellRead outputs.gcd)
              (.product (GCD.cellRead left) (GCD.cellRead right))) result)).eventTrace
                path.2.2.2.2))) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
