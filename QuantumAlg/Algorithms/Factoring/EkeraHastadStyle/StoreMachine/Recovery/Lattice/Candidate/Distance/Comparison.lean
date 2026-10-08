/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Distance.Comparison.Layout

/-!
# Actual eleven-instruction near-target comparison
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original native copy into a supplied scaling destination. -/
def copyOp (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx input output

/-- Actual source copy followed by the original three native left shifts. -/
def copyScaleInto (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (copyOp input output))
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output)

/-- Actual chronological store and paths after copying and multiplying by eight. -/
def copyScaleStep (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (copyScaleInto input output).Path :=
  let copied := BitWord.instructionStep (execution := model) (copyOp input output) store
  let shifted := ClassicalRoutines.Word.PowerOfTwo.shiftStep 3 output copied.1
  (shifted.1, (copied.2, shifted.2))

/-- The actual copy-and-shift interpreter preserves all incoming state blocks. -/
theorem copyScaleInto_execute (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (copyScaleInto input output).execute Reference state = state.mapClassical (fun entry =>
      let actual := copyScaleStep input output entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (copyOp input output))
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (copyOp input output) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := ClassicalRoutines.Word.PowerOfTwo.shiftStep 3 output before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (fun reference _history _ current =>
      ClassicalRoutines.Word.PowerOfTwo.shiftInto_execute 3 output reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The original upper-bound square is written by one native low-word multiplication. -/
def squareOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .mulLow width ctx (.product refs.upperBound refs.upperBound) refs.rangeSquare

/-- One native addition completes nine times the original range square. -/
def addRangeOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx
    (.product (writeInput refs.scaledRange) (writeInput refs.rangeSquare)) refs.scaledRange

/-- Actual comparison of the two stored unsigned scaled operands. -/
def compareOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx
    (.product (writeInput refs.scaledDistance) (writeInput refs.scaledRange)) refs.accepted

/-- The final native range addition precedes the actual stored-operand comparison. -/
def finishInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (addRangeOp refs))
    (BitWord.instruction (execution := model) (compareOp refs))

/-- Exact actual store and paths of the final addition and comparison. -/
def finishStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (finishInto refs).Path :=
  let added := BitWord.instructionStep (execution := model) (addRangeOp refs) store
  let compared := BitWord.instructionStep (execution := model) (compareOp refs) added.1
  (compared.1, (added.2, compared.2))

/-- Actual multiplication by eight precedes addition of the original range square. -/
def rangeInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange) (finishInto refs)

/-- Actual chronological range scale, addition and comparison stores. -/
def rangeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (rangeInto refs).Path :=
  let scaled := copyScaleStep (writeInput refs.rangeSquare) refs.scaledRange store
  let finished := finishStep refs scaled.1
  (finished.1, (scaled.2, finished.2))

/-- Actual squaring precedes the original scaled-range suffix. -/
def squareRangeInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (squareOp refs)) (rangeInto refs)

/-- Exact actual squaring and scaled-range stores with both native paths. -/
def squareRangeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (squareRangeInto refs).Path :=
  let squared := BitWord.instructionStep (execution := model) (squareOp refs) store
  let ranged := rangeStep refs squared.1
  (ranged.1, (squared.2, ranged.2))

/-- The original eleven native instructions execute in their original chronological order. -/
def scaleInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (copyScaleInto refs.distance refs.scaledDistance) (squareRangeInto refs)

/-- Complete actual stores and native paths of the scaled near-target decision. -/
def scaleStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (scaleInto refs).Path :=
  let distance := copyScaleStep refs.distance refs.scaledDistance store
  let ranged := squareRangeStep refs distance.1
  (ranged.1, (distance.2, ranged.2))

/-- Final addition and actual comparison preserve the full incoming execution state. -/
theorem finishInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (finishInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := finishStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (addRangeOp refs))
    (BitWord.instruction (execution := model) (compareOp refs))
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (addRangeOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (compareOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual range composition retains each incoming history and reference block. -/
theorem rangeInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (rangeInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := rangeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange)
    (finishInto refs)
    (fun before =>
      let actual := copyScaleStep (writeInput refs.rangeSquare) refs.scaledRange before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := finishStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      copyScaleInto_execute (writeInput refs.rangeSquare) refs.scaledRange reference current)
    (fun reference _history _ current => finishInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual squareRange composition retains each incoming history and reference block. -/
theorem squareRangeInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (squareRangeInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := squareRangeStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (BitWord.instruction (execution := model) (squareOp refs))
    (rangeInto refs)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (squareOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := rangeStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (fun reference _history _ current => rangeInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual scale composition retains each incoming history and reference block. -/
theorem scaleInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scaleInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := scaleStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (copyScaleInto refs.distance refs.scaledDistance)
    (squareRangeInto refs)
    (fun before =>
      let actual := copyScaleStep refs.distance refs.scaledDistance before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := squareRangeStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      copyScaleInto_execute refs.distance refs.scaledDistance reference current)
    (fun reference _history _ current => squareRangeInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
