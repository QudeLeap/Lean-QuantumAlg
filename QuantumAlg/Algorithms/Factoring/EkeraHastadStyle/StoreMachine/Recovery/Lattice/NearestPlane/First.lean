/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.First.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual first-coordinate nearest-plane circuit

The real dot and norm refreshes feed signed nearest division, whose stored
coefficient drives the actual coordinate updates. The full interpreter equation
records that coefficient's real branch history and every chronological store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Four actual stages compute the nearest coefficient and update the residual target. -/
def firstInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeDotRefresh.refreshInto refs.target refs.basis.first (numeratorDotRefs refs))
    (.seq (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct)))

/-- Actual division writes and coordinate writes, with the division's selected path. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct)).Path :=
  let divided := SignedWord.RoundedDiv.bodyStep refs.division store
  (LatticeArithmetic.pointStore (SignedWord.writeInput refs.division.output)
    refs.basis.first refs.target refs.reduceProduct divided.1,
      (divided.2, (((), ()), (((), ()), ((), ())))))

/-- Norm refresh feeds its actual resulting store into division and reduction. -/
def normReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq
      (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct))).Path :=
  let normed := LatticeNormRefresh.refreshStore refs.basis.first (denominatorNormRefs refs) store
  let reduced := divisionReductionStep refs normed
  (reduced.1, (((), (((), ()), ((), ()))), reduced.2))

/-- Complete chronological native updates and actual selected path of the first phase. -/
def firstStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (firstInto refs).Path :=
  let dotted := LatticeDotRefresh.refreshStore refs.target refs.basis.first
    (numeratorDotRefs refs) store
  let reduced := normReductionStep refs dotted
  (reduced.1, (((), (((), ()), ((), ()))), reduced.2))

private theorem divisionReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct)).execute Reference state =
      state.mapClassical (fun entry => ((divisionReductionStep refs entry.1).1,
        (entry.2, (divisionReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (SignedWord.RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.first refs.target refs.reduceProduct)
    (SignedWord.RoundedDiv.bodyStep refs.division)
    (fun store => (LatticeArithmetic.pointStore (SignedWord.writeInput refs.division.output)
      refs.basis.first refs.target refs.reduceProduct store, (((), ()), (((), ()), ((), ())))))
    (SignedWord.RoundedDiv.body_execute refs.division)
    (by
      intro ref history _ current
      refine (LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem normReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (Circuit.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (SignedWord.writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct))).execute Reference state =
      state.mapClassical (fun entry => ((normReductionStep refs entry.1).1,
        (entry.2, (normReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
    (.seq (SignedWord.RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.first refs.target refs.reduceProduct))
    (fun store => (LatticeNormRefresh.refreshStore refs.basis.first
      (denominatorNormRefs refs) store,
      ((), (((), ()), ((), ()))))) (divisionReductionStep refs)
    (by
      intro ref history _ current
      refine (LatticeNormRefresh.refreshInto_execute refs.basis.first
        (denominatorNormRefs refs) ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (divisionReduction_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete real execution preserves prior histories and full quantum-reference correlations. -/
theorem firstInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (firstInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((firstStep refs entry.1).1, (entry.2, (firstStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeDotRefresh.refreshInto refs.target refs.basis.first (numeratorDotRefs refs))
    (.seq (LatticeNormRefresh.refreshInto refs.basis.first (denominatorNormRefs refs))
      (.seq (SignedWord.RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.first refs.target refs.reduceProduct)))
    (fun store => (LatticeDotRefresh.refreshStore refs.target refs.basis.first
      (numeratorDotRefs refs) store, ((), (((), ()), ((), ()))))) (normReductionStep refs)
    (by
      intro ref history _ current
      refine (LatticeDotRefresh.refreshInto_execute refs.target refs.basis.first
        (numeratorDotRefs refs) ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (normReduction_execute refs)
    Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneFirst
