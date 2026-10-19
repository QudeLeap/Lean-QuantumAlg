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
def refreshInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) : Circuit model ctx ctx :=
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

/-- Six actual Gram updates and their value-bearing selected paths. -/
def refreshStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (refreshInto (model := model) basis refs).Path :=
  let first := entryStep (model := model) basis refs .g11 store
  let second := entryStep (model := model) basis refs .g21 first.1
  let third := entryStep (model := model) basis refs .g31 second.1
  let fourth := entryStep (model := model) basis refs .g22 third.1
  let fifth := entryStep (model := model) basis refs .g32 fourth.1
  let sixth := entryStep (model := model) basis refs .g33 fifth.1
  (sixth.1, (first.2, (second.2, (third.2, (fourth.2, (fifth.2, sixth.2))))))

lemma refreshStep_store {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    (refreshStep (model := model) basis refs store).1 =
      refreshStore basis refs store := rfl

/-- The complete chronological path depends on the actual input store. -/
def refreshPath {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width) (store : Store ctx) :
    (refreshInto (model := model) basis refs).Path :=
  (refreshStep (model := model) basis refs store).2

/-- Full actual execution preserves histories and all quantum-reference correlations. -/
lemma refreshInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (basis : LatticeState.BasisRefs ctx width)
    (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (refreshInto (model := model) basis refs).execute environment Reference state =
      state.mapClassical (fun record =>
        let actual := refreshStep (model := model) basis refs record.1
        (actual.1, (record.2.1, (record.2.2, actual.2)))) := by
  simp only [refreshInto, refreshStep, Circuit.execute_seq, entryInto_execute,
    State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual caller read outside the seven written cells is unchanged. -/
lemma refreshInto_callerFrame (basis : LatticeState.BasisRefs ctx width)
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
