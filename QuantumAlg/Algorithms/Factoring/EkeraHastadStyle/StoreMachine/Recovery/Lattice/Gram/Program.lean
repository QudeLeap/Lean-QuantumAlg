/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Entry

/-!
# Actual in-place Gram matrix refresh

Six five-instruction dot refreshes overwrite arbitrary previous Gram values.
The circuit uses the original six destinations and one shared product word.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Refresh all six Gram entries directly, with no preceding accumulator clear. -/
def refreshInto (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width) :
    Circuit ctx ctx :=
  .seq (entryInto basis refs .g11)
    (.seq (entryInto basis refs .g21)
      (.seq (entryInto basis refs .g31)
        (.seq (entryInto basis refs .g22)
          (.seq (entryInto basis refs .g32) (entryInto basis refs .g33)))))

/-- The actual chronological stores of the thirty native instructions. -/
def refreshStore (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (store : Store ctx) : Store ctx :=
  entryStore basis refs .g33 (entryStore basis refs .g32 (entryStore basis refs .g22
    (entryStore basis refs .g31 (entryStore basis refs .g21 (entryStore basis refs .g11 store)))))

/-- The unique path of each five-operation dot refresh. -/
def entryPath (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width) (entry : Entry) :
    (entryInto basis refs entry).Path := ((), (((), ()), ((), ())))

/-- The complete chronological path of the six actual refreshes. -/
def refreshPath (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width) :
    (refreshInto basis refs).Path :=
  (entryPath basis refs .g11, entryPath basis refs .g21, entryPath basis refs .g31,
    entryPath basis refs .g22, entryPath basis refs .g32, entryPath basis refs .g33)

/-- Full actual execution preserves histories and all quantum-reference correlations. -/
theorem refreshInto_execute (basis : LatticeState.BasisRefs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (refreshInto basis refs).execute Reference state = state.mapClassical (fun entry =>
      (refreshStore basis refs entry.1, (entry.2, refreshPath basis refs))) := by
  simp only [refreshInto, entryInto, LatticeDotRefresh.refreshInto, LatticeDot.coordinateAccumulate,
    Circuit.execute_seq, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- Every actual caller read outside the seven written cells is unchanged. -/
theorem refreshInto_callerFrame (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ cell, metricCellKey refs cell ∉ other.storageKeys) :
    (refreshStore basis refs store).read other = store.read other := by
  unfold refreshStore
  rw [entryInto_callerFrame _ _ .g33 _ other (avoids .g33) (avoids .product)]
  rw [entryInto_callerFrame _ _ .g32 _ other (avoids .g32) (avoids .product)]
  rw [entryInto_callerFrame _ _ .g22 _ other (avoids .g22) (avoids .product)]
  rw [entryInto_callerFrame _ _ .g31 _ other (avoids .g31) (avoids .product)]
  rw [entryInto_callerFrame _ _ .g21 _ other (avoids .g21) (avoids .product)]
  rw [entryInto_callerFrame _ _ .g11 _ other (avoids .g11) (avoids .product)]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeMetricMachine
