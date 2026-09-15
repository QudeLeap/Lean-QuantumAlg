/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Point.Program.Frames

/-!
# Actual candidate-point mathematical correctness
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem coefficient_coordinate_correct (refs : Refs ctx width) (coordinate : Coordinate)
    (store : Store ctx) (left right : Int)
    (leftRep : RawSignedRepresents (store.read (sourceInput refs (centerSource coordinate))) left)
    (rightRep : RawSignedRepresents
      (store.read (sourceInput refs (offsetSource coordinate))) right) :
    RawSignedRepresents ((store.applyOp (coefficientOp refs coordinate)).read
      (writeInput (pointRef refs.coefficient coordinate))) (left + right) := by
  change RawSignedRepresents ((store.applyOp (coefficientOp refs coordinate)).read
    (.storage (coefficientOp refs coordinate).outputRef.toCStorageRef)) _
  rw [Store.read_applyOp_output]
  exact rawSignedWordRepresents_add _ _ left right leftRep rightRep

/-- Three actual additions represent the exact integer coefficient sum modulo the original width. -/
theorem coefficientInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (center offset : NumberTheory.IntegerPoint3)
    (centerRep : LatticeArithmetic.PointRawRepresents store refs.center center)
    (offsetRep : LatticeArithmetic.PointRawRepresents store refs.offset offset) :
    LatticeArithmetic.PointRawRepresents (coefficientStore refs store) refs.coefficient
      (center.add offset) := by
  unfold coefficientStore
  refine ⟨?_, ?_, ?_⟩
  · rw [coefficient_output_frame refs separation _ .third .first (by decide),
      coefficient_output_frame refs separation _ .second .first (by decide)]
    exact coefficient_coordinate_correct refs .first store _ _ centerRep.1 offsetRep.1
  · rw [coefficient_output_frame refs separation _ .third .second (by decide)]
    apply coefficient_coordinate_correct refs .second
    · rw [coefficient_source_frame refs separation _ .first .centerSecond]
      exact centerRep.2.1
    · rw [coefficient_source_frame refs separation _ .first .offsetSecond]
      exact offsetRep.2.1
  · apply coefficient_coordinate_correct refs .third
    · rw [coefficient_source_frame refs separation _ .second .centerThird,
        coefficient_source_frame refs separation _ .first .centerThird]
      exact centerRep.2.2
    · rw [coefficient_source_frame refs separation _ .second .offsetThird,
        coefficient_source_frame refs separation _ .first .offsetThird]
      exact offsetRep.2.2

/-- Exact mathematical columns of the original ordered reduced basis. -/
def columnValue (basis : NumberTheory.IntegerBasis3) : Coordinate → NumberTheory.IntegerPoint3
  | .first => (basis.first.1, basis.second.1, basis.third.1)
  | .second => (basis.first.2.1, basis.second.2.1, basis.third.2.1)
  | .third => (basis.first.2.2, basis.second.2.2, basis.third.2.2)

/-- The raw basis representation yields the selected actual column. -/
theorem column_represents (refs : Refs ctx width) (store : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (rep : BasisRawRepresents store refs.basis basis)
    (coordinate : Coordinate) :
    LatticeArithmetic.PointRawRepresents store (columnRefs refs.basis coordinate)
      (columnValue basis coordinate) := by
  cases coordinate with
  | first => exact ⟨rep.1.1, rep.2.1.1, rep.2.2.1⟩
  | second => exact ⟨rep.1.2.1, rep.2.1.2.1, rep.2.2.2.1⟩
  | third => exact ⟨rep.1.2.2, rep.2.1.2.2, rep.2.2.2.2⟩

/-- The three column dot products are exactly the original integer lattice combination. -/
theorem linearCombination_eq_columnDots
    (basis : NumberTheory.IntegerBasis3) (coefficient : NumberTheory.IntegerPoint3) :
    basis.linearCombination coefficient =
      (NumberTheory.integerPointDot coefficient (columnValue basis .first),
        NumberTheory.integerPointDot coefficient (columnValue basis .second),
        NumberTheory.integerPointDot coefficient (columnValue basis .third)) := by
  apply Prod.ext
  · simp only [NumberTheory.IntegerBasis3.linearCombination,
      NumberTheory.IntegerPoint3.add, NumberTheory.IntegerPoint3.smul,
      NumberTheory.integerPointDot, columnValue]
    ring
  · apply Prod.ext <;>
      simp only [NumberTheory.IntegerBasis3.linearCombination,
        NumberTheory.IntegerPoint3.add, NumberTheory.IntegerPoint3.smul,
        NumberTheory.integerPointDot, columnValue] <;> ring

/-- One actual refresh represents its coefficient dot product with the selected basis column. -/
theorem coordinateCombination_correct (refs : Refs ctx width) (separation : Separation refs)
    (coordinate : Coordinate) (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (coefficient : NumberTheory.IntegerPoint3)
    (basisRep : BasisRawRepresents store refs.basis basis)
    (coefficientRep : LatticeArithmetic.PointRawRepresents store refs.coefficient coefficient) :
    RawSignedRepresents ((combinationStore refs coordinate store).read
      (writeInput (pointRef refs.point coordinate)))
      (NumberTheory.integerPointDot coefficient (columnValue basis coordinate)) :=
  (LatticeDotRefresh.refreshInto_correct refs.coefficient (columnRefs refs.basis coordinate)
    (dotRefs refs coordinate) (combination_separation refs separation coordinate) store
    coefficient (columnValue basis coordinate) coefficientRep
    (column_represents refs store basis basisRep coordinate)).1

/-- Three actual dot refreshes compute the original lattice combination and retain coefficients. -/
theorem pointInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (coefficient : NumberTheory.IntegerPoint3)
    (basisRep : BasisRawRepresents store refs.basis basis)
    (coefficientRep : LatticeArithmetic.PointRawRepresents store refs.coefficient coefficient) :
    LatticeArithmetic.PointRawRepresents (pointStore refs store) refs.point
        (basis.linearCombination coefficient) ∧
      LatticeArithmetic.PointRawRepresents
        (pointStore refs store) refs.coefficient coefficient := by
  have basisFirst := basis_after_combination refs separation .first store basis basisRep
  have coeffFirst := coefficient_after_combination refs separation .first store _ coefficientRep
  have basisSecond := basis_after_combination refs separation .second _ basis basisFirst
  have coeffSecond := coefficient_after_combination refs separation .second _ _ coeffFirst
  refine ⟨?_, coefficient_after_combination refs separation .third _ _ coeffSecond⟩
  rw [linearCombination_eq_columnDots]
  unfold pointStore
  refine ⟨?_, ?_, ?_⟩
  · rw [combination_output_frame refs separation .third .first (by decide),
      combination_output_frame refs separation .second .first (by decide)]
    exact coordinateCombination_correct refs separation .first store basis coefficient
      basisRep coefficientRep
  · rw [combination_output_frame refs separation .third .second (by decide)]
    exact coordinateCombination_correct refs separation .second _ basis coefficient
      basisFirst coeffFirst
  · exact coordinateCombination_correct refs separation .third _ basis coefficient
      basisSecond coeffSecond

/-- Original modular inputs; no initial scratch values or extra signed-range premises are needed. -/
def InitialConditions (store : Store ctx) (refs : Refs ctx width)
    (basis : NumberTheory.IntegerBasis3) (center offset : NumberTheory.IntegerPoint3) : Prop :=
  BasisRawRepresents store refs.basis basis ∧
    LatticeArithmetic.PointRawRepresents store refs.center center ∧
      LatticeArithmetic.PointRawRepresents store refs.offset offset

/-- Both exact mathematical outputs and the full original caller frame of actual execution. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (center offset : NumberTheory.IntegerPoint3) : Prop where
  coefficient : LatticeArithmetic.PointRawRepresents after refs.coefficient (center.add offset)
  point : LatticeArithmetic.PointRawRepresents after refs.point
    (basis.linearCombination (center.add offset))
  callerFrame : CallerFrame refs before after

/-- The actual eighteen native instructions realize the original candidate construction. -/
theorem candidatePointInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (center offset : NumberTheory.IntegerPoint3)
    (initial : InitialConditions store refs basis center offset) :
    Outcome refs store (candidateStep refs store).1 basis center offset := by
  have coefficients := coefficientInto_correct refs separation store center offset
    initial.2.1 initial.2.2
  have basisLoaded := basis_after_coefficient refs separation store basis initial.1
  have point := pointInto_correct refs separation (coefficientStore refs store)
    basis (center.add offset) basisLoaded coefficients
  exact ⟨point.2, point.1, candidatePointInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePointMachine
