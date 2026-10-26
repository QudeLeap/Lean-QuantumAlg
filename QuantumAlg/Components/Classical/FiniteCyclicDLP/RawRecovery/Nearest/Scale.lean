/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Scale
import all QuantumAlg.Util.NearestResidue

/-!
# Paid nearest-integer frequency scaling

The complete product is rounded by an actual resized and right-shifted
denominator.  Exact division produces the nearest integer; a second division
reduces its possible upper-end wrap modulo the order.  Every operation belongs
to this actual program and its chronological native event trace.
-/

namespace QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest

open Execution
open RawRecovery.Native (scaleRead scaleProductOp scaleDivisionShape)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Real input and scratch cells used by the nearest scaling instruction sequence. -/
structure ScaleRefs (ctx : RuntimeCtx kind) (width : Nat) where
  raw : CInputRef ctx (.unsignedWord width)
  order : CInputRef ctx (.unsignedWord (width + 1))
  denominator : CInputRef ctx (.unsignedWord (width + 1))
  product : CWriteRef ctx (.unsignedWord (width + (width + 1)))
  half : CWriteRef ctx (.unsignedWord (width + (width + 1)))
  division : CWriteRef ctx (scaleDivisionShape width)
  output : CWriteRef ctx (.unsignedWord width)

namespace ScaleRefs

def halfResizeOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.wordResize (width + 1) (width + (width + 1)) ctx refs.denominator refs.half

def halfShiftOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.wordUnary .shiftRight (width + (width + 1)) ctx (scaleRead refs.half) refs.half

def roundOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.wordBinary .add (width + (width + 1)) ctx
    (.product (scaleRead refs.product) (scaleRead refs.half)) refs.product

def divideOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.divRem (width + (width + 1)) (width + 1) ctx
    (.product (scaleRead refs.product) refs.denominator) refs.division

def reduceOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.divRem (width + (width + 1)) (width + 1) ctx
    (.product (.first (scaleRead refs.division)) refs.order) refs.division

def finishOp (refs : ScaleRefs ctx width) :=
  ClassicalOp.wordResize (width + 1) width ctx (.second (scaleRead refs.division)) refs.output

end ScaleRefs

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual seven-instruction nearest scaling and canonical-wrap program.
The stored denominator is loaded by the enclosing paid power-of-two loader. -/
def scaleBody (refs : ScaleRefs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
    (scaleProductOp refs.raw refs.order refs.product))
    (.seq (BitWord.instruction (execution := model) refs.halfResizeOp)
      (.seq (BitWord.instruction (execution := model) refs.halfShiftOp)
        (.seq (BitWord.instruction (execution := model) refs.roundOp)
          (.seq (BitWord.instruction (execution := model) refs.divideOp)
            (.seq (BitWord.instruction (execution := model) refs.reduceOp)
              (BitWord.instruction (execution := model) refs.finishOp))))))

/-- The actual returned path retains all seven chronological instruction results. -/
def scaleStep (refs : ScaleRefs ctx width) (store : Store ctx) :
    Store ctx × (scaleBody (model := model) refs).Path :=
  let first := BitWord.instructionStep (execution := model)
    (scaleProductOp refs.raw refs.order refs.product) store
  let second := BitWord.instructionStep (execution := model) refs.halfResizeOp first.1
  let third := BitWord.instructionStep (execution := model) refs.halfShiftOp second.1
  let fourth := BitWord.instructionStep (execution := model) refs.roundOp third.1
  let fifth := BitWord.instructionStep (execution := model) refs.divideOp fourth.1
  let sixth := BitWord.instructionStep (execution := model) refs.reduceOp fifth.1
  let seventh := BitWord.instructionStep (execution := model) refs.finishOp sixth.1
  (seventh.1, (first.2, (second.2, (third.2, (fourth.2, (fifth.2, (sixth.2, seventh.2)))))))

/-- The same program preserves all persistent services and arbitrary quantum
Reference correlations while recording its actual classical path. -/
lemma scaleBody_execute (refs : ScaleRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scaleBody (model := model) refs).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := scaleStep (model := model) refs entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  simp only [scaleBody, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Independent native coordinates for the actual nearest scaling sequence. -/
def scaleBodyEvents (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.mulFull width (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) (width + (width + 1)))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftRight (width + (width + 1)))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .add (width + (width + 1)))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem (width + (width + 1)) (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem (width + (width + 1)) (width + 1))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordResize (width + 1) width))]

/-- Every rounding and wrap operation occurs in the actual chronological ledger. -/
lemma scaleBody_eventTrace (refs : ScaleRefs ctx width)
    (path : (scaleBody (model := model) refs).Path) :
    (scaleBody (model := model) refs).eventTrace path =
      scaleBodyEvents (model := model) width := by
  change (BitWord.instruction (execution := model)
    (scaleProductOp refs.raw refs.order refs.product)).eventTrace path.1 ++
      ((BitWord.instruction (execution := model) refs.halfResizeOp).eventTrace path.2.1 ++
        ((BitWord.instruction (execution := model) refs.halfShiftOp).eventTrace path.2.2.1 ++
          ((BitWord.instruction (execution := model) refs.roundOp).eventTrace path.2.2.2.1 ++
            ((BitWord.instruction (execution := model) refs.divideOp).eventTrace
                path.2.2.2.2.1 ++
              ((BitWord.instruction (execution := model) refs.reduceOp).eventTrace
                  path.2.2.2.2.2.1 ++
                (BitWord.instruction (execution := model) refs.finishOp).eventTrace
                  path.2.2.2.2.2.2))))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The seven actual instructions are sequential and have native depth seven. -/
lemma scaleBody_depth (refs : ScaleRefs ctx width)
    (path : (scaleBody (model := model) refs).Path) :
    (scaleBody (model := model) refs).depth (fun _ => 1) path = 7 := rfl

end

end QuantumAlg.ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Nearest
