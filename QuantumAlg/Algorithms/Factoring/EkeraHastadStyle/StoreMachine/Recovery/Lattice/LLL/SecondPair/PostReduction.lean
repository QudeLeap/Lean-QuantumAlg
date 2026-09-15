/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction.Layout

/-!
# Actual final first-direction second-pair reduction

The actual refreshed dot product feeds the original first-direction division.
Its stored quotient drives the final third-row reduction in the same circuit
interpreter, preserving complete histories and quantum-reference blocks.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual division and row update for the final first-direction coefficient. -/
def divisionReductionInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (RoundedDiv.body refs.machine.division31)
    (LatticeArithmetic.pointReduce (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct)

/-- Actual division branch path and the six native third-row updates. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (divisionReductionInto refs).Path :=
  let divided := RoundedDiv.bodyStep refs.machine.division31 store
  (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
    refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct divided.1,
      (divided.2, (((), ()), (((), ()), ((), ())))))

/-- Execute the original refresh, division and first-to-third row reduction chronologically. -/
def postReductionInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.machine.basis.third refs.machine.basis.first
    (refreshG31Refs refs)) (divisionReductionInto refs)

/-- Actual final store and recorded path of all three post-reduction stages. -/
def postReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (postReductionInto refs).Path :=
  let refreshed := LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
    (refreshG31Refs refs) store
  let reduced := divisionReductionStep refs refreshed
  (reduced.1, (((), (((), ()), ((), ()))), reduced.2))

/-- The actual stored quotient feeds the final row reduction in the complete interpreter. -/
theorem divisionReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (divisionReductionInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((divisionReductionStep refs entry.1).1,
        (entry.2, (divisionReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (RoundedDiv.body refs.machine.division31)
    (LatticeArithmetic.pointReduce (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct)
    (RoundedDiv.bodyStep refs.machine.division31)
    (fun store => (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct store,
        (((), ()), (((), ()), ((), ())))))
    (RoundedDiv.body_execute refs.machine.division31) (by
      intro Reference History _ state
      refine (LatticeArithmetic.pointReduce_execute _ _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual final reduction uses the actual refreshed numerator without a second runtime. -/
theorem postReductionInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (postReductionInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((postReductionStep refs entry.1).1, (entry.2, (postReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto refs.machine.basis.third refs.machine.basis.first
      (refreshG31Refs refs)) (divisionReductionInto refs)
    (fun store => (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
      (refreshG31Refs refs) store, ((), (((), ()), ((), ())))))
    (divisionReductionStep refs) (by
      intro Reference History _ state
      refine (LatticeDotRefresh.refreshInto_execute _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (divisionReductionInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
