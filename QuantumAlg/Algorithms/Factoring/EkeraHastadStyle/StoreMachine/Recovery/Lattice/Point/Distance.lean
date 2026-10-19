/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Distance.Layout

/-!
# Actual initialized point squared distance
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
  {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual point subtraction precedes a self-dot refresh that overwrites the old accumulator. -/
def squaredDistanceInto [BitWord.Selected model] (refs : Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (LatticePointDifferenceMachine.pointDifferenceInto refs.difference)
    (LatticeDotRefresh.refreshInto refs.difference.difference refs.difference.difference
      (dotRefs refs))

/-- Actual chronological subtraction and self-dot stores, including every native path. -/
def distanceStep [BitWord.Selected model] (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (squaredDistanceInto refs).Path :=
  let difference := LatticePointDifferenceMachine.differenceStep (model := model)
    refs.difference store
  let squared := LatticeDotRefresh.refreshStep (model := model) refs.difference.difference
    refs.difference.difference (dotRefs refs) difference.1
  (squared.1, (difference.2, squared.2))

/-- All eight actual instructions preserve the complete incoming history and reference blocks. -/
lemma squaredDistanceInto_execute [BitWord.Selected model]
    (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (squaredDistanceInto refs).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := distanceStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [squaredDistanceInto, Circuit.execute_seq,
    LatticePointDifferenceMachine.pointDifferenceInto_execute,
    LatticeDotRefresh.refreshInto_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual distance circuit retains every read outside its five original output cells. -/
lemma squaredDistanceInto_callerFrame [BitWord.Selected model]
    (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (distanceStep refs store).1 := by
  intro shape other first second third squared product
  change (LatticeDotRefresh.refreshStore _ _ _
    (LatticePointDifferenceMachine.differenceStore refs.difference store)).read other = _
  rw [LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other squared product]
  apply LatticePointDifferenceMachine.pointDifferenceInto_callerFrame
  intro coordinate
  cases coordinate with
  | first => exact first
  | second => exact second
  | third => exact third

/-- Actual point difference, exact modular squared norm and the original complete caller frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (pointValue targetValue : NumberTheory.IntegerPoint3) : Prop where
  difference : LatticeArithmetic.PointRawRepresents after refs.difference.difference
    (pointValue.sub targetValue)
  squaredDistance : RawSignedRepresents (after.read (writeInput refs.squaredDistance))
    (NumberTheory.integerPointSquaredNorm (pointValue.sub targetValue) : Int)
  callerFrame : CallerFrame refs before after

/-- Explicit native initialization computes squared distance from arbitrary original scratch. -/
lemma squaredDistanceInto_correct [BitWord.Selected model]
    (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (pointValue targetValue : NumberTheory.IntegerPoint3)
    (initial : InitialConditions store refs pointValue targetValue) :
    Outcome refs store (distanceStep refs store).1 pointValue targetValue := by
  have difference := LatticePointDifferenceMachine.pointDifferenceInto_correct refs.difference
    separation.difference store pointValue targetValue initial.point initial.target
  have dot := LatticeDotRefresh.refreshInto_correct refs.difference.difference
    refs.difference.difference (dotRefs refs) ⟨separation.dot⟩
    (LatticePointDifferenceMachine.differenceStore refs.difference store)
    (pointValue.sub targetValue) (pointValue.sub targetValue) difference difference
  refine ⟨dot.2.1, ?_, squaredDistanceInto_callerFrame refs store⟩
  rw [← NumberTheory.integerPointDot_self]
  exact dot.1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSquaredDistanceMachine
