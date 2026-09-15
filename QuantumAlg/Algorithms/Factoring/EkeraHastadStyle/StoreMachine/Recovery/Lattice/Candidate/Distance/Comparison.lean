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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original native copy into a supplied scaling destination. -/
def copyOp (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx input output

/-- Actual source copy followed by the original three native left shifts. -/
def copyScaleInto (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (.classical (copyOp input output)) (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output)

/-- Actual chronological store and paths after copying and multiplying by eight. -/
def copyScaleStep (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx × (copyScaleInto input output).Path :=
  let shifted := ClassicalRoutines.Word.PowerOfTwo.shiftStep 3 output
    (store.applyOp (copyOp input output))
  (shifted.1, ((), shifted.2))

/-- The actual copy-and-shift interpreter preserves all incoming state blocks. -/
theorem copyScaleInto_execute (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (copyScaleInto input output).execute Reference state = state.mapClassical (fun entry =>
      ((copyScaleStep input output entry.1).1,
        (entry.2, (copyScaleStep input output entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (copyOp input output))
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto 3 output)
    (fun store => (store.applyOp (copyOp input output), ()))
    (ClassicalRoutines.Word.PowerOfTwo.shiftStep 3 output) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (copyOp input output)
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (ClassicalRoutines.Word.PowerOfTwo.shiftInto_execute 3 output) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

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
def finishInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (addRangeOp refs)) (.classical (compareOp refs))

/-- Exact actual store and paths of the final addition and comparison. -/
def finishStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (finishInto refs).Path :=
  ((store.applyOp (addRangeOp refs)).applyOp (compareOp refs), ((), ()))

/-- Actual multiplication by eight precedes addition of the original range square. -/
def rangeInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange) (finishInto refs)

/-- Actual chronological range scale, addition and comparison stores. -/
def rangeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (rangeInto refs).Path :=
  let scaled := copyScaleStep (writeInput refs.rangeSquare) refs.scaledRange store
  let finished := finishStep refs scaled.1
  (finished.1, (scaled.2, finished.2))

/-- Actual squaring precedes the original scaled-range suffix. -/
def squareRangeInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (squareOp refs)) (rangeInto refs)

/-- Exact actual squaring and scaled-range stores with both native paths. -/
def squareRangeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (squareRangeInto refs).Path :=
  let ranged := rangeStep refs (store.applyOp (squareOp refs))
  (ranged.1, ((), ranged.2))

/-- The original eleven native instructions execute in their original chronological order. -/
def scaleInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (copyScaleInto refs.distance refs.scaledDistance) (squareRangeInto refs)

/-- Complete actual stores and native paths of the scaled near-target decision. -/
def scaleStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (scaleInto refs).Path :=
  let distance := copyScaleStep refs.distance refs.scaledDistance store
  let ranged := squareRangeStep refs distance.1
  (ranged.1, (distance.2, ranged.2))

/-- Final addition and actual comparison preserve the full incoming execution state. -/
theorem finishInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finishInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((finishStep refs entry.1).1, (entry.2, (finishStep refs entry.1).2))) := by
  simp only [finishInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Actual range composition retains each incoming history and reference block. -/
theorem rangeInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (rangeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((rangeStep refs entry.1).1, (entry.2, (rangeStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (copyScaleInto (writeInput refs.rangeSquare) refs.scaledRange)
    (finishInto refs) (copyScaleStep (writeInput refs.rangeSquare) refs.scaledRange)
    (finishStep refs) (copyScaleInto_execute (writeInput refs.rangeSquare) refs.scaledRange)
    (finishInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual squareRange composition retains each incoming history and reference block. -/
theorem squareRangeInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (squareRangeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((squareRangeStep refs entry.1).1, (entry.2, (squareRangeStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (.classical (squareOp refs))
    (rangeInto refs) (fun store => (store.applyOp (squareOp refs), ()))
    (rangeStep refs) (by
      intro Reference History _ state
      refine (Circuit.execute_classical_mapClassical (squareOp refs) Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (rangeInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual scale composition retains each incoming history and reference block. -/
theorem scaleInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scaleInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((scaleStep refs entry.1).1, (entry.2, (scaleStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (copyScaleInto refs.distance refs.scaledDistance)
    (squareRangeInto refs) (copyScaleStep refs.distance refs.scaledDistance)
    (squareRangeStep refs) (copyScaleInto_execute refs.distance refs.scaledDistance)
    (squareRangeInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _


end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearTargetScale
