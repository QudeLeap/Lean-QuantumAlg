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
def reduceRefreshInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeArithmetic.pointReduce (writeInput refs.division.output)
    refs.basis.first refs.basis.second refs.reduceProduct)
    (LatticeNormRefresh.refreshInto refs.basis.second refs.refresh)

/-- Actual row reduction and norm refresh stores, with their eleven-operation path. -/
def reduceRefreshStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (reduceRefreshInto refs).Path :=
  let reduced := LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.first refs.basis.second refs.reduceProduct store
  (LatticeNormRefresh.refreshStore refs.basis.second refs.refresh reduced,
    ((((), ()), (((), ()), ((), ()))), ((), (((), ()), ((), ())))))

/-- The actual rounded quotient feeds the native row and norm updates. -/
def reductionPrefixInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (RoundedDiv.body refs.division) (reduceRefreshInto refs)

/-- The actual division path and the following eleven native writes. -/
def reductionPrefixStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (reductionPrefixInto refs).Path :=
  let divided := RoundedDiv.bodyStep refs.division store
  let reduced := reduceRefreshStep refs divided.1
  (reduced.1, (divided.2, reduced.2))

/-- Execute the complete original first-pair reduction and its actual Lovasz-selected branch. -/
def firstPairInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (reductionPrefixInto refs) (lovaszBranchInto refs)

/-- Complete actual chronological stores and recorded branches of the first-pair transition. -/
def firstPairStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstPairInto refs).Path :=
  let reduced := reductionPrefixStep refs store
  let selected := lovaszBranchStep refs reduced.1
  (selected.1, (reduced.2, selected.2))

/-- The actual reduced row feeds the norm computation while full histories and blocks survive. -/
theorem reduceRefreshInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reduceRefreshInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((reduceRefreshStep refs entry.1).1, (entry.2, (reduceRefreshStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct)
    (LatticeNormRefresh.refreshInto refs.basis.second refs.refresh)
    (fun store => (LatticeArithmetic.pointStore (writeInput refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct store,
        (((), ()), (((), ()), ((), ())))))
    (fun store => (LatticeNormRefresh.refreshStore refs.basis.second refs.refresh store,
      ((), (((), ()), ((), ())))))
    (by
      intro Reference History _ state
      refine (LatticeArithmetic.pointReduce_execute _ _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (by
      intro Reference History _ state
      refine (LatticeNormRefresh.refreshInto_execute _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual prefix execution preserves history and quantum-reference correlations. -/
theorem reductionPrefixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (reductionPrefixInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((reductionPrefixStep refs entry.1).1, (entry.2, (reductionPrefixStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (RoundedDiv.body refs.division) (reduceRefreshInto refs)
    (RoundedDiv.bodyStep refs.division) (reduceRefreshStep refs)
    (RoundedDiv.body_execute refs.division) (reduceRefreshInto_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Full actual first-pair execution uses the real division and comparison outcomes. -/
theorem firstPairInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstPairInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((firstPairStep refs entry.1).1, (entry.2, (firstPairStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (reductionPrefixInto refs) (lovaszBranchInto refs)
    (reductionPrefixStep refs) (lovaszBranchStep refs)
    (reductionPrefixInto_execute refs) (lovaszBranchInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
