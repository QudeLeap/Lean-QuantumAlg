/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Coordinate

/-!
# Actual nine-copy lattice row exchange

Three actual coordinate exchanges share one caller-owned scratch word. The
complete actual store and path retain all nine native copy operations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Execute the three original coordinate exchanges through the same actual scratch word. -/
def pointSwap (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  .seq (coordinateSwap left.first right.first scratch)
    (.seq (coordinateSwap left.second right.second scratch)
      (coordinateSwap left.third right.third scratch))

/-- The actual chronological stores after all three coordinate exchanges. -/
def pointSwapStore (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) : Store ctx :=
  coordinateSwapStore left.third right.third scratch
    (coordinateSwapStore left.second right.second scratch
      (coordinateSwapStore left.first right.first scratch store))

/-- Full actual execution preserves history and all quantum-reference blocks. -/
theorem pointSwap_execute (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pointSwap left right scratch).execute Reference state = state.mapClassical (fun entry =>
      (pointSwapStore left right scratch entry.1,
        (entry.2, (((), ((), ())), ((), ((), ())), ((), ((), ())))))) := by
  simp only [pointSwap, coordinateSwap, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Any caller read outside the full seven-cell actual footprint is preserved. -/
theorem pointSwap_callerFrame (left right : LatticeState.PointRefs ctx width)
    (scratch : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, pointSwapCellKey left right scratch cell ∉ other.storageKeys) :
    (pointSwapStore left right scratch store).read other = store.read other := by
  unfold pointSwapStore
  rw [coordinateSwap_callerFrame _ _ _ _ other
    (avoids .leftThird) (avoids .rightThird) (avoids .scratch),
    coordinateSwap_callerFrame _ _ _ _ other
      (avoids .leftSecond) (avoids .rightSecond) (avoids .scratch),
    coordinateSwap_callerFrame _ _ _ _ other
      (avoids .leftFirst) (avoids .rightFirst) (avoids .scratch)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSwap
