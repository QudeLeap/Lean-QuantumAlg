/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Selection

/-!
# Actual first-pair LLL transition

The original actual division output drives the row reduction. The refreshed
norm then drives the actual Lovasz comparison and its selected row-exchange
branch. Every stage consumes its predecessor's concrete store and path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Reduce the second basis row and refresh its actual squared-norm cell. -/
def reduceRefreshInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeArithmetic.pointReduce (model := model) (writeInput refs.division.output)
    refs.basis.first refs.basis.second refs.reduceProduct)
    (LatticeNormRefresh.refreshInto (model := model) refs.basis.second refs.refresh)

/-- Actual row reduction and norm refresh stores, with their eleven-operation path. -/
def reduceRefreshStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (reduceRefreshInto (model := model) refs).Path :=
  let reduced := LatticeArithmetic.pointStep (model := model) (writeInput refs.division.output)
    refs.basis.first refs.basis.second refs.reduceProduct store
  let refreshed := LatticeDotRefresh.refreshStep (model := model)
    refs.basis.second refs.basis.second
    (LatticeNormRefresh.dotRefs refs.refresh) reduced.1
  (refreshed.1, (reduced.2, refreshed.2))

/-- The actual rounded quotient feeds the native row and norm updates. -/
def reductionPrefixInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (RoundedDiv.body (model := model) refs.division)
    (reduceRefreshInto (model := model) refs)

/-- The actual division path and the following eleven native writes. -/
def reductionPrefixStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (reductionPrefixInto (model := model) refs).Path :=
  let divided := RoundedDiv.bodyStep (model := model) refs.division store
  let reduced := reduceRefreshStep (model := model) refs divided.1
  (reduced.1, (divided.2, reduced.2))

/-- Execute the complete original first-pair reduction and its actual Lovasz-selected branch. -/
def firstPairInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (reductionPrefixInto (model := model) refs) (lovaszBranchInto (model := model) refs)

/-- Complete actual chronological stores and recorded branches of the first-pair transition. -/
def firstPairStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstPairInto (model := model) refs).Path :=
  let reduced := reductionPrefixStep (model := model) refs store
  let selected := lovaszBranchStep (model := model) refs reduced.1
  (selected.1, (reduced.2, selected.2))

/-- The reduced row feeds the norm computation while histories and blocks survive. -/
theorem reduceRefreshInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reduceRefreshInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := reduceRefreshStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeArithmetic.pointReduce (model := model) (writeInput refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct)
    (LatticeNormRefresh.refreshInto (model := model) refs.basis.second refs.refresh)
    (fun before =>
      let actual := LatticeArithmetic.pointStep (model := model)
        (writeInput refs.division.output) refs.basis.first refs.basis.second
        refs.reduceProduct before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeDotRefresh.refreshStep (model := model)
        refs.basis.second refs.basis.second
        (LatticeNormRefresh.dotRefs refs.refresh) before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeArithmetic.pointReduce_execute _ _ _ _ reference current)
    (fun reference _history _ current =>
      LatticeNormRefresh.refreshInto_execute _ _ reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Complete actual prefix execution preserves history and quantum-reference correlations. -/
theorem reductionPrefixInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (reductionPrefixInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := reductionPrefixStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (RoundedDiv.body (model := model) refs.division)
    (reduceRefreshInto (model := model) refs)
    (fun before =>
      let actual := RoundedDiv.bodyStep (model := model) refs.division before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := reduceRefreshStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => RoundedDiv.body_execute refs.division reference current)
    (fun reference _history _ current => reduceRefreshInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Full actual first-pair execution uses the real division and comparison outcomes. -/
theorem firstPairInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (firstPairInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := firstPairStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (reductionPrefixInto (model := model) refs) (lovaszBranchInto (model := model) refs)
    (fun before =>
      let actual := reductionPrefixStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := lovaszBranchStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => reductionPrefixInto_execute refs reference current)
    (fun reference _history _ current => lovaszBranchInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
