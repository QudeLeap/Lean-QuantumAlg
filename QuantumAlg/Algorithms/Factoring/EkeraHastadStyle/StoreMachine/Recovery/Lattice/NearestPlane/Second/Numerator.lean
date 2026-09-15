/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Layout

/-!
# Actual second-coordinate nearest-plane numerator

The shared three-instruction product difference writes the numerator in place.
Its first product uses the output cell itself; the second product uses the
original single numerator scratch word.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The native product difference uses the output itself as first product scratch. -/
def numeratorInto (refs : Refs ctx width) : Circuit ctx ctx :=
  LatticeCross.coordinateCross (writeInput refs.g11) (writeInput refs.targetDotSecond)
    (writeInput refs.g21) (writeInput refs.targetDotFirst)
    refs.numerator refs.numerator refs.numeratorProduct

/-- The three actual chronological numerator updates. -/
def numeratorStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  LatticeCross.coordinateStore (writeInput refs.g11) (writeInput refs.targetDotSecond)
    (writeInput refs.g21) (writeInput refs.targetDotFirst)
    refs.numerator refs.numerator refs.numeratorProduct store

/-- The complete actual numerator interpreter retains history and quantum-reference blocks. -/
theorem numeratorInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (numeratorInto refs).execute Reference state = state.mapClassical (fun entry =>
      (numeratorStore refs entry.1, (entry.2, ((), ((), ()))))) := by
  exact LatticeCross.coordinateCross_execute _ _ _ _ _ _ _ Reference state

/-- Only the original two numerator words are modified. -/
theorem numeratorInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (notNumerator : refs.numerator.key ∉ other.storageKeys)
    (notProduct : refs.numeratorProduct.key ∉ other.storageKeys) :
    (numeratorStore refs store).read other = store.read other :=
  LatticeCross.coordinateCross_callerFrame _ _ _ _ _ _ _ _ _
    notNumerator notNumerator notProduct

/-- Distinct named phase cells survive the two numerator writes. -/
theorem numeratorInto_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) {shape : CShape} (other : CWriteRef ctx shape) (source : PhaseCell)
    (sourceKey : other.key = phaseCellKey refs source)
    (notNumerator : .numerator ≠ source) (notProduct : .numeratorProduct ≠ source) :
    (numeratorStore refs store).read (.storage other.toCStorageRef) =
      store.read (.storage other.toCStorageRef) := by
  apply numeratorInto_callerFrame
  · change refs.numerator.key ∉ [other.key]
    simpa only [List.mem_singleton, sourceKey, phaseCellKey] using
      separation.phaseCellKey_ne .numerator source notNumerator
  · change refs.numeratorProduct.key ∉ [other.key]
    simpa only [List.mem_singleton, sourceKey, phaseCellKey] using
      separation.phaseCellKey_ne .numeratorProduct source notProduct

/-- Actual multiplication and subtraction compute the cleared second numerator. -/
theorem numeratorInto_correct (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (store : Store ctx) (g11 g21 targetSecond targetFirst : Int)
    (g11Rep : RawSignedRepresents (store.read (writeInput refs.g11)) g11)
    (g21Rep : RawSignedRepresents (store.read (writeInput refs.g21)) g21)
    (targetSecondRep : RawSignedRepresents (store.read (writeInput refs.targetDotSecond))
      targetSecond)
    (targetFirstRep : RawSignedRepresents (store.read (writeInput refs.targetDotFirst))
      targetFirst) :
    RawSignedRepresents ((numeratorStore refs store).read (writeInput refs.numerator))
      (g11 * targetSecond - g21 * targetFirst) := by
  apply LatticeCross.coordinateCross_correct _ _ _ _ _ _ _ store
    _ _ _ g11 targetSecond g21 targetFirst g11Rep targetSecondRep g21Rep targetFirstRep
  · change refs.numerator.key ∉ [refs.g21.key]
    simpa only [List.mem_singleton, phaseCellKey] using
      separation.phaseCellKey_ne .numerator .g21 (by decide)
  · change refs.numerator.key ∉ [refs.targetDotFirst.key]
    simpa only [List.mem_singleton, phaseCellKey] using
      separation.phaseCellKey_ne .numerator .targetDotFirst (by decide)
  · exact separation.phaseCellKey_ne .numeratorProduct .numerator (by decide)

/-- The actual numerator restores all borrowed correlations for arbitrary incoming states. -/
theorem numeratorInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (numeratorInto refs).BorrowedRestored Reference state
      ((numeratorInto refs).execute Reference state) := by
  exact LatticeCross.coordinateCross_borrowedRestored _ _ _ _ _ _ _ Reference state

/-- The actual numerator has exactly three native instruction dependencies. -/
theorem numeratorInto_depth (refs : Refs ctx width) (path : (numeratorInto refs).Path) :
    (numeratorInto refs).depth (fun _ => 1) path = 3 := rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
