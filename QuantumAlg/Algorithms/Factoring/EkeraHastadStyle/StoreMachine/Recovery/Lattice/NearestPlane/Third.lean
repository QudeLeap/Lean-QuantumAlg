/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Sign
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.RoundedDiv.Execution

/-!
# Actual third-coordinate nearest-plane circuit

The real signed denominator is normalized into the existing magnitude word.
Its actual sign controls the numerator correction before actual rounded division
and the third-direction target reduction.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Normalize the actual denominator, correct the numerator, divide and update the target. -/
def thirdNormalizeInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (normalizeMagnitude (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (.seq (numeratorSignInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct)))

/-- The actual metric prefix feeds the complete signed third-coordinate reduction. -/
def thirdInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (thirdMetricPrefixInto refs) (thirdNormalizeInto refs)

/-- Actual division writes and target updates, recording the division's actual selected path. -/
def divisionReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct)).Path :=
  let divided := RoundedDiv.bodyStep refs.division store
  (LatticeArithmetic.pointStore (writeInput refs.division.output)
    refs.basis.third refs.target refs.reduceProduct divided.1,
      (divided.2, (((), ()), (((), ()), ((), ())))))

/-- The actual numerator correction feeds the actual division and coordinate updates. -/
def signReductionStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (Circuit.seq (numeratorSignInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct))).Path :=
  let corrected := numeratorSignStep refs store
  let reduced := divisionReductionStep refs corrected.1
  (reduced.1, (corrected.2, reduced.2))

/-- The complete chronological suffix state and its actual normalization and division flags. -/
def thirdNormalizeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (thirdNormalizeInto refs).Path :=
  let normalized := normalizationStep (writeInput refs.denominator)
    refs.division.negative refs.denominatorMagnitude store
  let reduced := signReductionStep refs normalized.1
  (reduced.1, (normalized.2, reduced.2))

/-- The complete third-phase chronological native updates and selected path. -/
def thirdStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (thirdInto refs).Path :=
  let reduced := thirdNormalizeStep refs (metricPrefixStore refs store)
  (reduced.1, (metricPrefixPath refs, reduced.2))

private theorem divisionReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct)).execute Reference state =
      state.mapClassical (fun entry => ((divisionReductionStep refs entry.1).1,
        (entry.2, (divisionReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (RoundedDiv.body refs.division)
    (LatticeArithmetic.pointReduce (writeInput refs.division.output)
      refs.basis.third refs.target refs.reduceProduct)
    (RoundedDiv.bodyStep refs.division)
    (fun store => (LatticeArithmetic.pointStore (writeInput refs.division.output)
      refs.basis.third refs.target refs.reduceProduct store,
      (((), ()), (((), ()), ((), ())))))
    (RoundedDiv.body_execute refs.division)
    (by
      intro ref history _ current
      refine (LatticeArithmetic.pointReduce_execute (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct ref current).trans ?_
      congr 1
      exact Subsingleton.elim _ _) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

private theorem signReduction_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.seq (numeratorSignInto refs)
      (Circuit.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct))).execute Reference state =
      state.mapClassical (fun entry => ((signReductionStep refs entry.1).1,
        (entry.2, (signReductionStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (numeratorSignInto refs)
    (.seq (RoundedDiv.body refs.division)
      (LatticeArithmetic.pointReduce (writeInput refs.division.output)
        refs.basis.third refs.target refs.reduceProduct))
    (numeratorSignStep refs) (divisionReductionStep refs)
    (numeratorSignInto_execute refs) (divisionReduction_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The actual normalization suffix preserves histories and full quantum-reference correlations. -/
theorem thirdNormalizeInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (thirdNormalizeInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((thirdNormalizeStep refs entry.1).1, (entry.2, (thirdNormalizeStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (normalizeMagnitude (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (.seq (numeratorSignInto refs)
      (.seq (RoundedDiv.body refs.division)
        (LatticeArithmetic.pointReduce (writeInput refs.division.output)
          refs.basis.third refs.target refs.reduceProduct)))
    (normalizationStep (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (signReductionStep refs)
    (normalizeMagnitude_execute (writeInput refs.denominator)
      refs.division.negative refs.denominatorMagnitude)
    (signReduction_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Complete actual execution records all real branches and preserves incoming correlations. -/
theorem thirdInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (thirdInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((thirdStep refs entry.1).1, (entry.2, (thirdStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (thirdMetricPrefixInto refs) (thirdNormalizeInto refs)
    (fun store => (metricPrefixStore refs store, metricPrefixPath refs)) (thirdNormalizeStep refs)
    (thirdMetricPrefixInto_execute refs) (thirdNormalizeInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
