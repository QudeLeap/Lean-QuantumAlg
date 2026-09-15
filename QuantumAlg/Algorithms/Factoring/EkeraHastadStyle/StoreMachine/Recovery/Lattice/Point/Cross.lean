/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Cross.Coordinate

/-!
# Actual three-dimensional cross product

Six native low-word multiplications and three subtractions produce the three
independent output coordinates. The two product words are reused in sequence.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual cross product, in first, second and third coordinate order. -/
def pointCrossInto (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (coordinateCross (writeInput left.second) (writeInput right.third)
      (writeInput left.third) (writeInput right.second) output.first productLeft productRight)
    (.seq (coordinateCross (writeInput left.third) (writeInput right.first)
        (writeInput left.first) (writeInput right.third) output.second productLeft productRight)
      (coordinateCross (writeInput left.first) (writeInput right.second)
        (writeInput left.second) (writeInput right.first) output.third productLeft productRight))

/-- The nine chronological native writes of the actual point circuit. -/
def pointStore (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Store ctx :=
  coordinateStore (writeInput left.first) (writeInput right.second)
    (writeInput left.second) (writeInput right.first) output.third productLeft productRight
    (coordinateStore (writeInput left.third) (writeInput right.first)
      (writeInput left.first) (writeInput right.third) output.second productLeft productRight
      (coordinateStore (writeInput left.second) (writeInput right.third)
        (writeInput left.third) (writeInput right.second) output.first productLeft productRight
        store))

/-- The full interpreter retains every incoming history and quantum-reference block. -/
theorem pointCrossInto_execute (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pointCrossInto left right output productLeft productRight).execute Reference state =
      state.mapClassical (fun entry => (pointStore left right output productLeft productRight
        entry.1, (entry.2, (((), ((), ())), (((), ((), ())), ((), ((), ()))))))) := by
  simp only [pointCrossInto, coordinateCross, ProductDifference.computeInto,
    Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Reads outside the five mutable words are unchanged. -/
theorem pointCrossInto_callerFrame (left right output : LatticeState.PointRefs ctx width)
    (productLeft productRight : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, mutableKey output productLeft productRight cell ∉ other.storageKeys) :
    (pointStore left right output productLeft productRight store).read other =
      store.read other := by
  unfold pointStore
  rw [coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputThird) (avoids .productLeft) (avoids .productRight),
    coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputSecond) (avoids .productLeft) (avoids .productRight),
    coordinateCross_callerFrame _ _ _ _ _ _ _ _ other
      (avoids .outputFirst) (avoids .productLeft) (avoids .productRight)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCross
