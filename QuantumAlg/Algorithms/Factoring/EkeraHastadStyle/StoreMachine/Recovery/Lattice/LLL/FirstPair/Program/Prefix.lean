/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Frame

/-!
# Actual first-pair arithmetic correctness

The actual rounded quotient reduces the second row. Its refreshed norm and the
retained first norm certify the later actual Lovasz decision on the original domain.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original actual numerator and denominator determine the stored reduction coefficient. -/
lemma division_coefficient {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    RawSignedRepresents ((RoundedDiv.bodyStep (model := model) refs.division store).1.read
      (writeInput refs.division.output)) basis.firstReductionCoefficient := by
  have positive : 0 < (store.read refs.division.denominator).toNat := by
    rw [initial.denominator]
    exact fits.denominatorPositive
  have result := RoundedDiv.body_outputRepresents refs.division separation.division store
    fits.widthPositive positive
  rw [initial.numerator, initial.denominator] at result
  exact result

/-- Division leaves all nine original basis coordinates intact. -/
lemma division_basis {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (RoundedDiv.bodyStep (model := model) refs.division store).1
      refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation row _ divisionCells (rep row)
    (division_frame refs store)
  intro cell member
  cases cell <;> decide

/-- The actual stored coefficient updates exactly the second row of the original pure reduction. -/
lemma reduction_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis)
    (coefficient : RawSignedRepresents (store.read (writeInput refs.division.output))
      basis.firstReductionCoefficient) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeArithmetic.pointStore (writeInput refs.division.output)
        refs.basis.first refs.basis.second refs.reduceProduct store)
      refs.basis basis.sizeReduceFirstPair.1 := by
  intro row
  cases row with
  | first =>
    apply row_raw_of_frame refs separation .first _ reductionCells (rep .first)
      (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [rowCells, basisTransitionCell, reductionCells]
  | second =>
    exact (LatticeArithmetic.pointReduce_correct _ _ _ _ separation.reduction store).1
      _ _ _ coefficient (rep .first) (rep .second)
  | third =>
    apply row_raw_of_frame refs separation .third _ reductionCells (rep .third)
      (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [rowCells, basisTransitionCell, reductionCells]

/-- Refresh computes the reduced second norm and preserves all three actual basis rows. -/
lemma refresh_basis_norm (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
        (LatticeNormRefresh.refreshStore refs.basis.second refs.refresh store) refs.basis basis ∧
      RawSignedRepresents
        ((LatticeNormRefresh.refreshStore refs.basis.second refs.refresh store).read
          (writeInput refs.metric.g22))
        (NumberTheory.integerPointSquaredNorm basis.second : Int) := by
  have refreshed := LatticeNormRefresh.refreshInto_correct _ _ separation.refresh store
    basis.second (rep .second)
  refine ⟨?_, ?_⟩
  · intro row
    apply row_raw_of_frame refs separation row _ refreshCells (rep row)
      (refresh_frame refs store)
    intro cell member
    cases cell <;> decide
  · rw [← refs.refreshNorm]
    exact refreshed.1

/-- The actual reduction prefix preserves the first norm input word exactly. -/
lemma reductionPrefix_g11 {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (reductionPrefixStep (model := model) refs store).1.read
      (writeInput refs.metric.g11) =
      store.read (writeInput refs.metric.g11) := by
  change (LatticeNormRefresh.refreshStore refs.basis.second refs.refresh
    (LatticeArithmetic.pointStore (writeInput refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct
      (RoundedDiv.bodyStep (model := model) refs.division store).1)).read
        (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g11)) = _
  rw [refresh_frame refs _ _ (metric_avoids refs separation .g11 refreshCells (by decide)),
    reduction_frame refs _ _ (metric_avoids refs separation .g11 reductionCells (by decide)),
    division_frame refs _ _ (metric_avoids refs separation .g11 divisionCells (by decide))]
  rfl

/-- The actual prefix produces the original reduced basis and both comparison inputs. -/
lemma reductionPrefix_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    LatticeMetricMachine.BasisRawRepresents (reductionPrefixStep (model := model) refs store).1
        refs.basis basis.sizeReduceFirstPair.1 ∧
      RawSignedRepresents ((reductionPrefixStep (model := model) refs store).1.read
        (writeInput refs.metric.g11)) (NumberTheory.integerPointSquaredNorm basis.first : Int) ∧
      RawSignedRepresents ((reductionPrefixStep (model := model) refs store).1.read
        (writeInput refs.metric.g22))
        (NumberTheory.integerPointSquaredNorm basis.sizeReduceFirstPair.1.second : Int) := by
  have divided := division_basis refs separation store basis initial.basisRep
  have coefficient := division_coefficient refs separation store basis initial fits
  have reduced := reduction_basis refs separation _ basis divided coefficient
  have refreshed := refresh_basis_norm refs separation _ basis.sizeReduceFirstPair.1 reduced
  refine ⟨refreshed.1, ?_, refreshed.2⟩
  rw [reductionPrefix_g11 refs separation store]
  have denominator := initial.denominator
  rw [refs.denominator] at denominator
  unfold RawSignedRepresents
  rw [denominator]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
