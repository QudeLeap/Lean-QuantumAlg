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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One actual native addition writes a center-plus-offset coefficient. -/
def coefficientOp (refs : Refs ctx width) (coordinate : Coordinate) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width))
      (.unsignedWord width) ctx ctx :=
  .wordBinary .add width ctx
    (.product (sourceInput refs (centerSource coordinate))
      (sourceInput refs (offsetSource coordinate))) (pointRef refs.coefficient coordinate)

/-- Three native additions compute the candidate coefficient in coordinate order. -/
def coefficientInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (coefficientOp refs .first))
    (.seq (.classical (coefficientOp refs .second)) (.classical (coefficientOp refs .third)))

/-- The actual store after all three coefficient additions. -/
def coefficientStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (coefficientOp refs .first)).applyOp (coefficientOp refs .second)).applyOp
    (coefficientOp refs .third)

/-- A coefficient and one original basis column determine one actual dot refresh. -/
def coordinateCombination (refs : Refs ctx width) (coordinate : Coordinate) : Circuit ctx ctx :=
  LatticeDotRefresh.refreshInto refs.coefficient (columnRefs refs.basis coordinate)
    (dotRefs refs coordinate)

/-- Actual five-instruction update for one lattice-point coordinate. -/
def combinationStore (refs : Refs ctx width) (coordinate : Coordinate) (store : Store ctx) :
    Store ctx :=
  LatticeDotRefresh.refreshStore refs.coefficient (columnRefs refs.basis coordinate)
    (dotRefs refs coordinate) store

/-- All three original dot refreshes reuse the same actual product cell. -/
def pointInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (coordinateCombination refs .first)
    (.seq (coordinateCombination refs .second) (coordinateCombination refs .third))

/-- The actual chronological three dot-refresh stores. -/
def pointStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  combinationStore refs .third (combinationStore refs .second (combinationStore refs .first store))

/-- Actual coefficient addition precedes the actual three-coordinate lattice combination. -/
def candidatePointInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (coefficientInto refs) (pointInto refs)

/-- Complete actual store and all eighteen chronological native instruction paths. -/
def candidateStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidatePointInto refs).Path :=
  (pointStore refs (coefficientStore refs store),
    (((), ((), ())), (((), (((), ()), ((), ()))),
      (((), (((), ()), ((), ()))), ((), (((), ()), ((), ())))))))

/-- The actual circuit preserves every incoming history and quantum-reference block. -/
theorem candidatePointInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidatePointInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((candidateStep refs entry.1).1, (entry.2, (candidateStep refs entry.1).2))) := by
  simp only [candidatePointInto, coefficientInto, pointInto, coordinateCombination,
    LatticeDotRefresh.refreshInto, LatticeDot.coordinateAccumulate, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
