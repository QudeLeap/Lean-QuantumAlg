/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Point.Difference.Layout

/-!
# Actual three-coordinate point subtraction

Three native subtraction instructions write the point difference directly.
The chronological store is proved to be the actual interpreter result.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- One actual modular subtraction writes the selected difference coordinate. -/
def differenceOp (refs : Refs ctx width) (cell : DifferenceCell) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) (.unsignedWord width)
      ctx ctx :=
  .wordBinary .sub width ctx
    (.product (sourceInput refs (pointSource cell)) (sourceInput refs (targetSource cell)))
    (differenceRef refs cell)

/-- Execute the three original native subtractions in coordinate order. -/
def pointDifferenceInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (differenceOp refs .first))
    (.seq (.classical (differenceOp refs .second)) (.classical (differenceOp refs .third)))

/-- The actual chronological three writes of the point subtraction. -/
def differenceStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((store.applyOp (differenceOp refs .first)).applyOp (differenceOp refs .second)).applyOp
    (differenceOp refs .third)

/-- All three actual writes preserve histories and quantum-reference correlations. -/
theorem pointDifferenceInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (pointDifferenceInto refs).execute Reference state = state.mapClassical (fun entry =>
      (differenceStore refs entry.1, (entry.2, ((), ((), ()))))) := by
  simp only [pointDifferenceInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual subtraction preserves every caller read outside its three output cells. -/
theorem pointDifferenceInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, differenceKey refs cell ∉ other.storageKeys) :
    (differenceStore refs store).read other = store.read other := by
  unfold differenceStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (differenceOp refs .third) other
      (avoids .third),
    Store.read_applyOp_of_not_mem_storageKeys _ (differenceOp refs .second) other
      (avoids .second),
    Store.read_applyOp_of_not_mem_storageKeys _ (differenceOp refs .first) other
      (avoids .first)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePointDifferenceMachine
