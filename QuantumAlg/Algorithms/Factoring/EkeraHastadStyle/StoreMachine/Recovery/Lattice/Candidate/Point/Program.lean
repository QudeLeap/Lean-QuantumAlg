/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.Program.Layout

/-!
# Actual candidate coefficient and lattice-point execution
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- One actual native addition writes a center-plus-offset coefficient. -/
def coefficientOp (refs : Refs ctx width) (coordinate : Coordinate) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx
    (.product (sourceInput refs (centerSource coordinate))
      (sourceInput refs (offsetSource coordinate))) (pointRef refs.coefficient coordinate)

/-- Three native additions compute the candidate coefficient in coordinate order. -/
def coefficientInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (coefficientOp refs .first))
    (.seq (BitWord.instruction (execution := model) (coefficientOp refs .second))
      (BitWord.instruction (execution := model) (coefficientOp refs .third)))

/-- The actual store after all three coefficient additions. -/
def coefficientStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (coefficientOp refs .first)).applyOp (coefficientOp refs .second)).applyOp
    (coefficientOp refs .third)

/-- A coefficient and one original basis column determine one actual dot refresh. -/
def coordinateCombination (refs : Refs ctx width) (coordinate : Coordinate) :
    Circuit model ctx ctx :=
  LatticeDotRefresh.refreshInto refs.coefficient (columnRefs refs.basis coordinate)
    (dotRefs refs coordinate)

/-- Actual five-instruction update for one lattice-point coordinate. -/
def combinationStore (refs : Refs ctx width) (coordinate : Coordinate) (store : Store ctx) :
    Store ctx :=
  LatticeDotRefresh.refreshStore refs.coefficient (columnRefs refs.basis coordinate)
    (dotRefs refs coordinate) store

/-- All three original dot refreshes reuse the same actual product cell. -/
def pointInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (coordinateCombination refs .first)
    (.seq (coordinateCombination refs .second) (coordinateCombination refs .third))

/-- The actual chronological three dot-refresh stores. -/
def pointStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  combinationStore refs .third (combinationStore refs .second (combinationStore refs .first store))

/-- Actual coefficient addition precedes the actual three-coordinate lattice combination. -/
def candidatePointInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (coefficientInto refs) (pointInto refs)

/-- Complete actual store and all eighteen chronological native instruction paths. -/
def candidateStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidatePointInto refs).Path :=
  let first := BitWord.instructionStep (execution := model) (coefficientOp refs .first) store
  let second := BitWord.instructionStep (execution := model) (coefficientOp refs .second) first.1
  let third := BitWord.instructionStep (execution := model) (coefficientOp refs .third) second.1
  let dotFirst := LatticeDotRefresh.refreshStep (model := model) refs.coefficient
    (columnRefs refs.basis .first) (dotRefs refs .first) third.1
  let dotSecond := LatticeDotRefresh.refreshStep (model := model) refs.coefficient
    (columnRefs refs.basis .second) (dotRefs refs .second) dotFirst.1
  let dotThird := LatticeDotRefresh.refreshStep (model := model) refs.coefficient
    (columnRefs refs.basis .third) (dotRefs refs .third) dotSecond.1
  (dotThird.1, ((first.2, (second.2, third.2)),
    (dotFirst.2, (dotSecond.2, dotThird.2))))

/-- The actual circuit preserves every incoming history and quantum-reference block. -/
lemma candidatePointInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePointInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := candidateStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [candidatePointInto, coefficientInto, pointInto, coordinateCombination,
    Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    LatticeDotRefresh.refreshInto_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
