/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Gram

/-!
# Complete actual second-direction reduction

The original signed numerator and denominator capacity bounds specialize actual
rounded division. Its stored coefficient drives the third-row reduction and
remains in the final actual store, together with the retained first norm.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original numeric bounds identify the actual stored second-direction quotient. -/
theorem division_coefficient (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (numerator : RawSignedRepresents (store.read refs.division32.numerator)
      basis.secondReductionNumerator)
    (denominator : RawSignedRepresents (store.read refs.division32.denominator)
      basis.secondReductionDenominator) (fits : Fits width basis) :
    RawSignedRepresents ((RoundedDiv.bodyStep refs.division32 store).1.read
      (writeInput refs.division32.output)) basis.sizeReduceSecondPair.2.1 := by
  have denominatorCast : (basis.secondReductionDenominator.toNat : Int) =
      basis.secondReductionDenominator := Int.toNat_of_nonneg (le_of_lt fits.denominatorPositive)
  have positive : 0 < basis.secondReductionDenominator.toNat := by
    have positiveCast : (0 : Int) < (basis.secondReductionDenominator.toNat : Int) := by
      rw [denominatorCast]
      exact fits.denominatorPositive
    exact_mod_cast positiveCast
  have capacity : basis.secondReductionDenominator.toNat < CShape.wordModulus width := by
    have castFits : (basis.secondReductionDenominator.toNat : Int) <
        (CShape.wordModulus width : Int) := by
      rw [denominatorCast]
      exact fits.denominatorFits
    exact_mod_cast castFits
  have represented : RawSignedRepresents (store.read refs.division32.denominator)
      (basis.secondReductionDenominator.toNat : Int) := by
    rw [denominatorCast]
    exact denominator
  have divided := RoundedDiv.body_outputRepresents_of_raw refs.division32 separation.division32
    store basis.secondReductionNumerator basis.secondReductionDenominator.toNat
    fits.widthPositive positive numerator fits.numeratorFits represented capacity
  rw [denominatorCast] at divided
  exact divided

/-- Actual rounded division preserves all nine represented basis coordinates. -/
theorem division_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents (RoundedDiv.bodyStep refs.division32 store).1
      refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation.phase row _ divisionCells (rep row)
    (division_frame refs store)
  intro cell member
  cases cell <;> decide

/-- The actual second-direction coefficient updates exactly the third original basis row. -/
theorem reduction_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis)
    (coefficient : RawSignedRepresents (store.read (writeInput refs.division32.output))
      basis.sizeReduceSecondPair.2.1) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeArithmetic.pointStore (writeInput refs.division32.output)
        refs.basis.second refs.basis.third refs.reduceProduct store)
      refs.basis (secondPairPrefixResult basis) := by
  intro row
  cases row with
  | first =>
    apply row_raw_of_frame refs separation.phase .first _ reductionCells (rep .first)
      (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [rowCells, basisTransitionCell, reductionCells]
  | second =>
    apply row_raw_of_frame refs separation.phase .second _ reductionCells (rep .second)
      (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [rowCells, basisTransitionCell, reductionCells]
  | third =>
    exact (LatticeArithmetic.pointReduce_correct _ _ _ _ separation.reduction store).1
      _ _ _ coefficient (rep .second) (rep .third)

/-- The third-row update retains the actual stored coefficient exactly. -/
theorem reduction_coefficient (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (LatticeArithmetic.pointStore (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct store).read
      (writeInput refs.division32.output) = store.read (writeInput refs.division32.output) :=
  reduction_frame refs store _ (write_avoids refs separation.phase refs.division32.output
    (.division32 .output) rfl reductionCells (by decide))

/-- Complete actual prefix execution retains the original first squared-norm input word. -/
theorem secondPairPrefixInto_g11 (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (secondPairPrefixStep refs store).1.read (writeInput refs.metric.g11) =
      store.read (writeInput refs.metric.g11) :=
  secondPairPrefixInto_callerFrame refs store _
    (metric_avoids refs separation.phase .g11 mutableCells (by decide))

/-- Actual prefix output basis, retained coefficient, first-norm word and complete read frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.basis (secondPairPrefixResult basis)
  coefficient : RawSignedRepresents (after.read (writeInput refs.division32.output))
    basis.sizeReduceSecondPair.2.1
  firstNorm : after.read (writeInput refs.metric.g11) = before.read (writeInput refs.metric.g11)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    FrameAvoids refs mutableCells other → after.read other = before.read other

/-- Complete actual prefix correctness holds on precisely the original input domain. -/
theorem secondPairPrefixInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    Outcome refs store (secondPairPrefixStep refs store).1 basis := by
  have prepared := refreshInputs_correct refs separation store basis initial
  have coefficient := division_coefficient refs separation (refreshInputsStep refs store).1
    basis prepared.2.1 prepared.2.2 fits
  have dividedBasis := division_basis refs separation _ basis prepared.1
  have reducedBasis := reduction_basis refs separation _ basis dividedBasis coefficient
  refine ⟨reducedBasis, ?_, secondPairPrefixInto_g11 refs separation store,
    secondPairPrefixInto_callerFrame refs store⟩
  change RawSignedRepresents ((LatticeArithmetic.pointStore (writeInput refs.division32.output)
    refs.basis.second refs.basis.third refs.reduceProduct
      (RoundedDiv.bodyStep refs.division32 (refreshInputsStep refs store).1).1).read
        (writeInput refs.division32.output)) _
  rw [reduction_coefficient refs separation]
  exact coefficient

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
