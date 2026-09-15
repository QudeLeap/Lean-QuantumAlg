/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Second.Numerator
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual second-coordinate nearest-plane circuit

The real metric prefix feeds the real numerator, rounded division and target
reduction. Every branch of the division is selected from the actual store;
the complete interpreter equation retains its recorded path.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual metrics, numerator and nearest coefficient drive the second target reduction. -/
def secondInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (secondPrefixInto refs)
    (.seq (numeratorInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct)))

/-- Actual division and reduction writes, with the selected division path. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct)).Path :=
  let divided := RoundedDiv.bodyStep refs.division store
  (LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.second refs.target refs.reduceProduct divided.1,
      (divided.2, (((), ()), (((), ()), ((), ())))))

/-- The numerator's actual store feeds the actual signed division and coordinate updates. -/
def numeratorReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (numeratorInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct))).Path :=
  let reduced := divisionReductionStep refs (numeratorStore refs store)
  (reduced.1, (((), ((), ())), reduced.2))

/-- The complete chronological store and actual selected path of the second phase. -/
def secondStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (secondInto refs).Path :=
  let reduced := numeratorReductionStep refs (secondPrefixStore refs store)
  (reduced.1, (prefixPath refs, reduced.2))

private theorem divisionReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct)).execute Reference state =
      state.mapClassical (fun entry => ((divisionReductionStep refs entry.1).1,
        (entry.2, (divisionReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.second refs.target refs.reduceProduct)
    (RoundedDiv.bodyStep refs.division)
    (fun store => (LatticeArithmetic.pointStore (writeInput refs.division.output)
      refs.basis.second refs.target refs.reduceProduct store,
      (((), ()), (((), ()), ((), ())))))
    (RoundedDiv.body_execute refs.division)
    (by
      intro ref history _ current
      refine (LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem numeratorReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (numeratorInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct))).execute Reference state =
      state.mapClassical (fun entry => ((numeratorReductionStep refs entry.1).1,
        (entry.2, (numeratorReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (numeratorInto refs)
    (.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.second refs.target refs.reduceProduct))
    (fun store => (numeratorStore refs store, ((), ((), ())))) (divisionReductionStep refs)
    (by
      intro ref history _ current
      refine (numeratorInto_execute refs ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (divisionReduction_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual execution preserves prior histories and full quantum-reference correlations. -/
theorem secondInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((secondStep refs entry.1).1, (entry.2, (secondStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (secondPrefixInto refs)
    (.seq (numeratorInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.second refs.target refs.reduceProduct)))
    (fun store => (secondPrefixStore refs store, prefixPath refs)) (numeratorReductionStep refs)
    (secondPrefixInto_execute refs) (numeratorReduction_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneSecond
