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

/-- Actual fourteen-operation squared-area refresh with its fixed native path. -/
def areaStep (left right : LatticeState.PointRefs ctx width)
    (refs : LatticeAreaRefresh.Refs ctx width)
    (store : Store ctx) : Store ctx × (LatticeAreaRefresh.refreshInto left right refs).Path :=
  (LatticeAreaRefresh.refreshStore left right refs store,
    ((((), ((), ())), (((), ((), ())), ((), ((), ())))), ((), (((), ()), ((), ())))))

/-- The first and second actual direction reductions compose in chronological order. -/
def sizeReductionInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeSecondPairMachine.secondPairPrefixInto refs.machine)
    (LatticeSecondPairPostReduction.postReductionInto refs.post)

/-- Both actual direction quotients and row-update paths are retained. -/
def sizeReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (sizeReductionInto refs).Path :=
  let first := LatticeSecondPairMachine.secondPairPrefixStep refs.machine store
  let second := LatticeSecondPairPostReduction.postReductionStep refs.post first.1
  (second.1, (first.2, second.2))

/-- Refresh the final area and then use the actual areas to select the second-Lovasz branch. -/
def area13BranchInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.third
    refs.area13)
    (LatticeSecondLovaszBranch.branchInto refs.branch)

/-- Actual second area feeds the actual stored comparison and selected exchange. -/
def area13BranchStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (area13BranchInto refs).Path :=
  let area := areaStep refs.machine.basis.first refs.machine.basis.third refs.area13 store
  let selected := LatticeSecondLovaszBranch.branchStep refs.branch area.1
  (selected.1, (area.2, selected.2))

/-- Refresh both original areas before their actual second-Lovasz selection. -/
def areaBranchInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.second
    refs.area12)
    (area13BranchInto refs)

/-- Actual first area feeds the second refresh and the selected branch. -/
def areaBranchStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (areaBranchInto refs).Path :=
  let area := areaStep refs.machine.basis.first refs.machine.basis.second refs.area12 store
  let selected := area13BranchStep refs area.1
  (selected.1, (area.2, selected.2))

/-- Execute both original reductions, both area refreshes and the actual selected second test. -/
def secondPairInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (sizeReductionInto refs) (areaBranchInto refs)

/-- The complete actual second-pair final store and chronological path. -/
def secondPairStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondPairInto refs).Path :=
  let reduced := sizeReductionStep refs store
  let selected := areaBranchStep refs reduced.1
  (selected.1, (reduced.2, selected.2))

/-- The fourteen actual area writes preserve histories and complete quantum-reference blocks. -/
theorem area_execute (left right : LatticeState.PointRefs ctx width)
    (refs : LatticeAreaRefresh.Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (LatticeAreaRefresh.refreshInto left right refs).execute Reference state =
      state.mapClassical (fun entry => ((areaStep left right refs entry.1).1,
        (entry.2, (areaStep left right refs entry.1).2))) := by
  refine (LatticeAreaRefresh.refreshInto_execute left right refs Reference state).trans ?_
  congr 1

/-- Both actual reduction interpreters compose without losing any state correlations. -/
theorem sizeReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (sizeReductionInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((sizeReductionStep refs entry.1).1, (entry.2, (sizeReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeSecondPairMachine.secondPairPrefixInto refs.machine)
    (LatticeSecondPairPostReduction.postReductionInto refs.post)
    (LatticeSecondPairMachine.secondPairPrefixStep refs.machine)
    (LatticeSecondPairPostReduction.postReductionStep refs.post)
    (LatticeSecondPairMachine.secondPairPrefixInto_execute refs.machine)
    (LatticeSecondPairPostReduction.postReductionInto_execute refs.post) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual final-area refresh feeds the complete actual branch interpreter. -/
theorem area13BranchInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (area13BranchInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((area13BranchStep refs entry.1).1, (entry.2, (area13BranchStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.third refs.area13)
    (LatticeSecondLovaszBranch.branchInto refs.branch)
    (areaStep refs.machine.basis.first refs.machine.basis.third refs.area13)
    (LatticeSecondLovaszBranch.branchStep refs.branch)
    (area_execute refs.machine.basis.first refs.machine.basis.third refs.area13)
    (LatticeSecondLovaszBranch.branchInto_execute refs.branch) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Both actual area refreshes feed the actual selected row exchange in the complete state. -/
theorem areaBranchInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (areaBranchInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((areaBranchStep refs entry.1).1, (entry.2, (areaBranchStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeAreaRefresh.refreshInto refs.machine.basis.first refs.machine.basis.second refs.area12)
    (area13BranchInto refs)
    (areaStep refs.machine.basis.first refs.machine.basis.second refs.area12)
    (area13BranchStep refs)
    (area_execute refs.machine.basis.first refs.machine.basis.second refs.area12)
    (area13BranchInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual second-pair execution follows its refreshed operands and actual decisions. -/
theorem secondPairInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPairInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondPairStep refs entry.1).1, (entry.2, (secondPairStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (sizeReductionInto refs) (areaBranchInto refs)
    (sizeReductionStep refs) (areaBranchStep refs) (sizeReductionInto_execute refs)
    (areaBranchInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
