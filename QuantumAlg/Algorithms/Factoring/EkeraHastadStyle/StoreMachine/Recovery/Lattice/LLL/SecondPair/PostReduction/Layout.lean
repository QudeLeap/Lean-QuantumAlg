/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Frame

/-!
# Original final second-pair reduction layout

The final first-direction reduction reuses the original prefix's allocation.
Its original contract needs only the basis and first norm initially, together
with its own refresh, division and row-reduction separation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory
open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned post-reduction cells, reusing the prefix allocation. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the machine stage. -/
  machine : LatticeSecondPairMachine.Refs ctx width
  numerator : machine.division31.numerator = SignedWord.writeInput machine.metric.g31
  denominator : machine.division31.denominator = SignedWord.writeInput machine.metric.g11

/-- The refresh package whose accumulator is the live `g31` metric word. -/
abbrev refreshG31Refs {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : LatticeDotRefresh.Refs ctx width where
  dot := refs.machine.metric.g31
  dotRole := refs.machine.metric.g31Role
  product := refs.machine.refreshG21Product
  productRole := refs.machine.refreshG21ProductRole

/-- Local separation for refresh, division, and first-to-third point reduction. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  phase : LatticeSecondPairMachine.PhaseSeparation refs.machine
  refresh : LatticeDotRefresh.Separation refs.machine.basis.third refs.machine.basis.first
    (refreshG31Refs refs)
  division : SignedWord.RoundedDiv.Separation refs.machine.division31
  reduction : LatticeArithmetic.PointReduceSeparation
    (SignedWord.writeInput refs.machine.division31.output) refs.machine.basis.first
      refs.machine.basis.third refs.machine.reduceProduct

/-- The rounded first-direction coefficient of the already second-reduced third row. -/
def postReductionCoefficient (basis : NumberTheory.IntegerBasis3) : Int :=
  NumberTheory.nearestIntegerCoefficient
    (NumberTheory.integerPointDot basis.third basis.first)
    (NumberTheory.integerPointSquaredNorm basis.first)

/-- The pure final first-direction operation of second-pair size reduction. -/
def postReductionResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  basis.reduceThirdByFirst (postReductionCoefficient basis)

/-- The post-prefix coefficient is the second pair's final first-direction coefficient. -/
lemma postReductionCoefficient_secondPairPrefixResult
    (basis : NumberTheory.IntegerBasis3) :
    postReductionCoefficient (LatticeSecondPairMachine.secondPairPrefixResult basis) =
      basis.sizeReduceSecondPair.2.2 := rfl

/-- Completing the post-prefix reduction produces the full second-pair result. -/
lemma postReductionResult_secondPairPrefixResult (basis : NumberTheory.IntegerBasis3) :
    postReductionResult (LatticeSecondPairMachine.secondPairPrefixResult basis) =
      basis.sizeReduceSecondPair.1 := rfl

/-- The original actual represented basis and first squared-norm word. -/
structure Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis
  firstNorm : RawSignedRepresents (store.read (writeInput refs.machine.metric.g11))
    (NumberTheory.integerPointSquaredNorm basis.first : Int)

/-- Exactly the original division domain for the final first-direction quotient. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  widthPositive : 0 < width
  denominatorPositive : 0 < NumberTheory.integerPointSquaredNorm basis.first
  denominatorFits : NumberTheory.integerPointSquaredNorm basis.first < CShape.wordModulus width
  numeratorFits : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width
    (NumberTheory.integerPointDot basis.third basis.first)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
