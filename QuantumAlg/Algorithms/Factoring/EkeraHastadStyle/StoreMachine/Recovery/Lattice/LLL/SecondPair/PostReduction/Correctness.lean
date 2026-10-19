/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction.Frame

/-!
# Actual final first-direction reduction correctness

The actual dot product and retained first norm determine the stored rounded
coefficient under the original numeric conditions. The actual third-row update
uses and preserves that coefficient while retaining every caller read outside
its original mutable footprint.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual dot refresh preserves the complete represented basis. -/
lemma refresh_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
        (refreshG31Refs refs) store) refs.machine.basis basis := by
  intro row
  apply LatticeSecondPairMachine.row_raw_of_frame refs.machine separation.phase row _
    refreshCells (rep row) (refresh_frame refs store)
  intro cell member
  cases cell <;> decide

/-- The original actual first norm survives numerator refresh exactly. -/
lemma refresh_denominator (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
      (refreshG31Refs refs) store).read refs.machine.division31.denominator =
      store.read (writeInput refs.machine.metric.g11) := by
  rw [refs.denominator]
  exact refresh_frame refs store _ (LatticeSecondPairMachine.metric_avoids refs.machine
    separation.phase .g11 refreshCells (by decide))

/-- The actual refreshed dot product and retained norm produce the original rounded coefficient. -/
lemma refreshed_division_coefficient {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    RawSignedRepresents ((RoundedDiv.bodyStep (model := model) refs.machine.division31
      (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
        (refreshG31Refs refs) store)).1.read (writeInput refs.machine.division31.output))
      (postReductionCoefficient basis) := by
  have dot := (LatticeDotRefresh.refreshInto_correct _ _ _ separation.refresh store
    basis.third basis.first (initial.basisRep .third) (initial.basisRep .first)).1
  apply RoundedDiv.body_outputRepresents_of_raw refs.machine.division31 separation.division _
    (NumberTheory.integerPointDot basis.third basis.first)
    (NumberTheory.integerPointSquaredNorm basis.first) fits.widthPositive fits.denominatorPositive
  · rw [refs.numerator]
    exact dot
  · exact fits.numeratorFits
  · rw [refresh_denominator refs separation store]
    exact initial.firstNorm
  · exact fits.denominatorFits

/-- Actual final-direction division preserves all represented basis coordinates. -/
lemma division_basis {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (RoundedDiv.bodyStep (model := model) refs.machine.division31 store).1
      refs.machine.basis basis := by
  intro row
  apply LatticeSecondPairMachine.row_raw_of_frame refs.machine separation.phase row _
    divisionCells (rep row) (division_frame refs store)
  intro cell member
  cases cell <;> decide

/-- The actual stored first-direction coefficient updates exactly the third basis row. -/
lemma reduction_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (coefficient : RawSignedRepresents (store.read (writeInput refs.machine.division31.output))
      (postReductionCoefficient basis)) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
        refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct store)
      refs.machine.basis (postReductionResult basis) := by
  intro row
  cases row with
  | first =>
    apply LatticeSecondPairMachine.row_raw_of_frame refs.machine separation.phase .first _
      LatticeSecondPairMachine.reductionCells (rep .first) (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [LatticeSecondPairMachine.rowCells,
      LatticeSecondPairMachine.basisTransitionCell, LatticeSecondPairMachine.reductionCells]
  | second =>
    apply LatticeSecondPairMachine.row_raw_of_frame refs.machine separation.phase .second _
      LatticeSecondPairMachine.reductionCells (rep .second) (reduction_frame refs store)
    intro cell member
    cases cell <;> simp_all [LatticeSecondPairMachine.rowCells,
      LatticeSecondPairMachine.basisTransitionCell, LatticeSecondPairMachine.reductionCells]
  | third =>
    exact (LatticeArithmetic.pointReduce_correct _ _ _ _ separation.reduction store).1
      _ _ _ coefficient (rep .first) (rep .third)

/-- The final actual row update retains the actual coefficient word exactly. -/
lemma reduction_coefficient (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (LatticeArithmetic.pointStore (writeInput refs.machine.division31.output)
      refs.machine.basis.first refs.machine.basis.third refs.machine.reduceProduct store).read
        (writeInput refs.machine.division31.output) =
      store.read (writeInput refs.machine.division31.output) :=
  reduction_frame refs store _ (LatticeSecondPairMachine.write_avoids refs.machine
    separation.phase refs.machine.division31.output (.division31 .output) rfl
    LatticeSecondPairMachine.reductionCells (by decide))

/-- Actual final basis, retained coefficient and first norm, and complete caller read frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.machine.basis
    (postReductionResult basis)
  coefficient : RawSignedRepresents (after.read (writeInput refs.machine.division31.output))
    (postReductionCoefficient basis)
  firstNorm : after.read (writeInput refs.machine.metric.g11) =
    before.read (writeInput refs.machine.metric.g11)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    LatticeSecondPairMachine.FrameAvoids refs.machine mutableCells other →
      after.read other = before.read other

/-- Actual final first-direction reduction realizes the original result on the original domain. -/
lemma postReductionInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    Outcome refs store (postReductionStep (model := model) refs store).1 basis := by
  have refreshedBasis := refresh_basis refs separation store basis initial.basisRep
  have coefficient := refreshed_division_coefficient refs separation store basis initial fits
  have dividedBasis := division_basis refs separation _ basis refreshedBasis
  have reducedBasis := reduction_basis refs separation _ basis dividedBasis coefficient
  refine ⟨reducedBasis, ?_, postReductionInto_g11 refs separation store,
    postReductionInto_callerFrame refs store⟩
  change RawSignedRepresents ((LatticeArithmetic.pointStore
    (writeInput refs.machine.division31.output) refs.machine.basis.first refs.machine.basis.third
    refs.machine.reduceProduct (RoundedDiv.bodyStep (model := model) refs.machine.division31
      (LatticeDotRefresh.refreshStore refs.machine.basis.third refs.machine.basis.first
        (refreshG31Refs refs) store)).1).read (writeInput refs.machine.division31.output)) _
  rw [reduction_coefficient refs separation]
  exact coefficient

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
