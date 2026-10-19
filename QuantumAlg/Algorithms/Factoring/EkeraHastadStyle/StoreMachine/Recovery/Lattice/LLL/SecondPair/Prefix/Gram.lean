/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Frame

/-!
# Actual Gram-derived second-reduction operands

Both dot refreshes preserve the original basis. The actual refreshed words and
the three original retained entries determine the two original integer Gram
expressions in the actual division input cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual dot refresh retains every original basis row. -/
lemma refresh21_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first
        (refreshG21Refs refs) store) refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation.phase row _ refresh21Cells (rep row)
    (refresh21_frame refs store)
  intro cell member
  cases cell <;> decide

/-- Actual dot refresh retains every original basis row. -/
lemma refresh32_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
        (refreshG32Refs refs) store) refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation.phase row _ refresh32Cells (rep row)
    (refresh32_frame refs store)
  intro cell member
  cases cell <;> decide

/-- Actual store after both original dot products are refreshed. -/
def refreshedDotsStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second (refreshG32Refs refs)
    (LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first (refreshG21Refs refs) store)

/-- All three original rows survive both actual dot refreshes. -/
lemma refreshedDots_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents (refreshedDotsStore refs store) refs.basis basis :=
  refresh32_basis refs separation _ basis (refresh21_basis refs separation store basis rep)

/-- Every other Gram word remains exactly unchanged by the two actual refreshes. -/
lemma refreshedDots_metric (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (cell : LatticeMetricMachine.MetricCell)
    (not21 : cell ≠ .g21) (not32 : cell ≠ .g32) :
    (refreshedDotsStore refs store).read (writeInput (LatticeMetricMachine.metricCellRef
      refs.metric cell)) = store.read (writeInput (LatticeMetricMachine.metricCellRef
        refs.metric cell)) := by
  have avoids21 := metric_avoids refs separation.phase cell refresh21Cells (by
    cases cell <;> simp_all [metricTransitionCell, refresh21Cells])
  have avoids32 := metric_avoids refs separation.phase cell refresh32Cells (by
    cases cell <;> simp_all [metricTransitionCell, refresh32Cells])
  unfold refreshedDotsStore
  rw [refresh32_frame refs _ _ avoids32, refresh21_frame refs _ _ avoids21]

/-- The five original integer Gram values used by the second-direction formulas. -/
def inputValues (basis : NumberTheory.IntegerBasis3) : LatticeSecondReductionInputs.InputCell → Int
  | .g11 => NumberTheory.integerPointSquaredNorm basis.first
  | .g21 => NumberTheory.integerPointDot basis.second basis.first
  | .g31 => NumberTheory.integerPointDot basis.third basis.first
  | .g22 => NumberTheory.integerPointSquaredNorm basis.second
  | .g32 => NumberTheory.integerPointDot basis.third basis.second

/-- Two actual refreshes and the three original retained entries provide all five Gram operands. -/
lemma refreshedDots_values (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (initial : Initial refs store basis) :
    LatticeSecondReductionInputs.InputsRepresents (reductionInputs refs)
      (refreshedDotsStore refs store) (inputValues basis) := by
  have firstDot := (LatticeDotRefresh.refreshInto_correct _ _ _ separation.refreshG21 store
    basis.second basis.first (initial.basisRep .second) (initial.basisRep .first)).1
  have middleBasis := refresh21_basis refs separation store basis initial.basisRep
  have secondDot := (LatticeDotRefresh.refreshInto_correct _ _ _ separation.refreshG32 _
    basis.third basis.second (middleBasis .third) (middleBasis .second)).1
  intro cell
  cases cell with
  | g11 =>
    change RawSignedRepresents ((refreshedDotsStore refs store).read
      (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g11))) _
    rw [refreshedDots_metric refs separation store .g11 (by decide) (by decide)]
    exact initial.firstNorm
  | g21 =>
    change RawSignedRepresents ((LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
      (refreshG32Refs refs) _).read
        (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g21))) _
    rw [refresh32_frame refs _ _
      (metric_avoids refs separation.phase .g21 refresh32Cells (by decide))]
    exact firstDot
  | g31 =>
    change RawSignedRepresents ((refreshedDotsStore refs store).read
      (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g31))) _
    rw [refreshedDots_metric refs separation store .g31 (by decide) (by decide)]
    exact initial.thirdFirstDot
  | g22 =>
    change RawSignedRepresents ((refreshedDotsStore refs store).read
      (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g22))) _
    rw [refreshedDots_metric refs separation store .g22 (by decide) (by decide)]
    exact initial.secondNorm
  | g32 => exact secondDot

/-- Actual arithmetic of both division inputs preserves the entire original represented basis. -/
lemma inputs_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
        refs.reductionInputs store) refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation.phase row _ inputsCells (rep row) (inputs_frame refs store)
  intro cell member
  cases cell <;> decide

/-- The actual division input store contains the original basis and both Gram expressions. -/
lemma refreshInputs_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3) (initial : Initial refs store basis) :
    LatticeMetricMachine.BasisRawRepresents
      (refreshInputsStep (model := model) refs store).1 refs.basis basis ∧
      RawSignedRepresents
        ((refreshInputsStep (model := model) refs store).1.read refs.division32.numerator)
        basis.secondReductionNumerator ∧
      RawSignedRepresents
        ((refreshInputsStep (model := model) refs store).1.read refs.division32.denominator)
        basis.secondReductionDenominator := by
  have represented := refreshedDots_values refs separation store basis initial
  have values := LatticeSecondReductionInputs.secondReductionInputsInto_correct _ _
    separation.inputs (refreshedDotsStore refs store) (inputValues basis) represented
  have basisRep := inputs_basis refs separation _ basis
    (refreshedDots_basis refs separation store basis initial.basisRep)
  refine ⟨basisRep, ?_, ?_⟩
  · rw [refs.division32Numerator]
    change RawSignedRepresents
      ((LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
        refs.reductionInputs (refreshedDotsStore refs store)).read
          (writeInput refs.reductionInputs.nu32)) _
    simpa only [inputValues, NumberTheory.IntegerBasis3.secondReductionNumerator] using values.1
  · rw [refs.division32Denominator]
    change RawSignedRepresents
      ((LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
        refs.reductionInputs (refreshedDotsStore refs store)).read
          (writeInput refs.reductionInputs.d32)) _
    simpa only [inputValues, NumberTheory.IntegerBasis3.secondReductionDenominator,
      NumberTheory.integerPointAreaSquared_eq_gram,
      NumberTheory.integerPointDot_comm basis.first basis.second, pow_two]
      using values.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
