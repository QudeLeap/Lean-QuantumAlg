/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program.Layout

/-!
# Complete actual second-pair transition

The two actual row reductions feed both actual squared-area refreshes and the
actual second-Lovasz selection. Every stage consumes the preceding concrete
store and carries its actual execution path in the one circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual fourteen-operation squared-area refresh with its fixed native path. -/
def areaStep (left right : LatticeState.PointRefs ctx width)
    (refs : LatticeAreaRefresh.Refs ctx width)
    (store : Store ctx) :
    Store ctx × (LatticeAreaRefresh.refreshInto (model := model) left right refs).Path :=
  LatticeAreaRefresh.refreshStep (model := model) left right refs store

/-- The first and second actual direction reductions compose in chronological order. -/
def sizeReductionInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeSecondPairMachine.secondPairPrefixInto refs.machine)
    (LatticeSecondPairPostReduction.postReductionInto refs.post)

/-- Both actual direction quotients and row-update paths are retained. -/
def sizeReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (sizeReductionInto (model := model) refs).Path :=
  let first := LatticeSecondPairMachine.secondPairPrefixStep (model := model)
    refs.machine store
  let second := LatticeSecondPairPostReduction.postReductionStep (model := model)
    refs.post first.1
  (second.1, (first.2, second.2))

/-- Refresh the final area and then use the actual areas to select the second-Lovasz branch. -/
def area13BranchInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.third
    refs.area13)
    (LatticeSecondLovaszBranch.branchInto refs.branch)

/-- Actual second area feeds the actual stored comparison and selected exchange. -/
def area13BranchStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (area13BranchInto (model := model) refs).Path :=
  let area := areaStep (model := model)
    refs.machine.basis.first refs.machine.basis.third refs.area13 store
  let selected := LatticeSecondLovaszBranch.branchStep (model := model) refs.branch area.1
  (selected.1, (area.2, selected.2))

/-- Refresh both original areas before their actual second-Lovasz selection. -/
def areaBranchInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.second
    refs.area12)
    (area13BranchInto (model := model) refs)

/-- Actual first area feeds the second refresh and the selected branch. -/
def areaBranchStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (areaBranchInto (model := model) refs).Path :=
  let area := areaStep (model := model)
    refs.machine.basis.first refs.machine.basis.second refs.area12 store
  let selected := area13BranchStep (model := model) refs area.1
  (selected.1, (area.2, selected.2))

/-- Execute both original reductions, both area refreshes and the actual selected second test. -/
def secondPairInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (sizeReductionInto (model := model) refs) (areaBranchInto (model := model) refs)

/-- The complete actual second-pair final store and chronological path. -/
def secondPairStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondPairInto (model := model) refs).Path :=
  let reduced := sizeReductionStep (model := model) refs store
  let selected := areaBranchStep (model := model) refs reduced.1
  (selected.1, (reduced.2, selected.2))

/-- The fourteen actual area writes preserve histories and complete quantum-reference blocks. -/
theorem area_execute (left right : LatticeState.PointRefs ctx width)
    (refs : LatticeAreaRefresh.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (LatticeAreaRefresh.refreshInto (model := model) left right refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := areaStep (model := model) left right refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  LatticeAreaRefresh.refreshInto_execute left right refs Reference state

/-- Both actual reduction interpreters compose without losing any state correlations. -/
theorem sizeReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (sizeReductionInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := sizeReductionStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeSecondPairMachine.secondPairPrefixInto (model := model) refs.machine)
    (LatticeSecondPairPostReduction.postReductionInto (model := model) refs.post)
    (fun before =>
      let actual := LatticeSecondPairMachine.secondPairPrefixStep (model := model)
        refs.machine before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeSecondPairPostReduction.postReductionStep (model := model)
        refs.post before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeSecondPairMachine.secondPairPrefixInto_execute refs.machine reference current)
    (fun reference _history _ current =>
      LatticeSecondPairPostReduction.postReductionInto_execute refs.post reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual final-area refresh feeds the complete actual branch interpreter. -/
theorem area13BranchInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (area13BranchInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := area13BranchStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeAreaRefresh.refreshInto (model := model)
      refs.machine.basis.first refs.machine.basis.third refs.area13)
    (LatticeSecondLovaszBranch.branchInto (model := model) refs.branch)
    (fun before =>
      let actual := areaStep (model := model)
        refs.machine.basis.first refs.machine.basis.third refs.area13 before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeSecondLovaszBranch.branchStep (model := model)
        refs.branch before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      area_execute _ _ _ reference current)
    (fun reference _history _ current =>
      LatticeSecondLovaszBranch.branchInto_execute refs.branch reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Both actual area refreshes feed the actual selected row exchange in the complete state. -/
theorem areaBranchInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (areaBranchInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := areaBranchStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeAreaRefresh.refreshInto (model := model)
      refs.machine.basis.first refs.machine.basis.second refs.area12)
    (area13BranchInto (model := model) refs)
    (fun before =>
      let actual := areaStep (model := model)
        refs.machine.basis.first refs.machine.basis.second refs.area12 before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := area13BranchStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => area_execute _ _ _ reference current)
    (fun reference _history _ current => area13BranchInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual second-pair execution follows its refreshed operands and actual decisions. -/
theorem secondPairInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondPairInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := secondPairStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (sizeReductionInto (model := model) refs) (areaBranchInto (model := model) refs)
    (fun before =>
      let actual := sizeReductionStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := areaBranchStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => sizeReductionInto_execute refs reference current)
    (fun reference _history _ current => areaBranchInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
