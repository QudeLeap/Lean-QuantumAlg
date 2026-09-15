/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz.Frame

/-!
# Actual second-Lovasz branch correctness

The actual original area readings determine the stored comparison bit. Its
selected arm realizes the original pure basis result, retaining the first row
and decision bit, with no additional area-to-basis disjointness premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual comparison retains every represented basis row. -/
theorem comparison_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents (LatticeLovasz.secondLovaszStore refs.lovasz store)
      refs.basis basis := by
  intro row
  cases row with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstFirst)) basis.first.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .firstFirst comparisonCells (by decide))]
      exact (rep .first).1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstSecond)) basis.first.2.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .firstSecond comparisonCells (by decide))]
      exact (rep .first).2.1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstThird)) basis.first.2.2
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .firstThird comparisonCells (by decide))]
      exact (rep .first).2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .secondFirst)) basis.second.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .secondFirst comparisonCells (by decide))]
      exact (rep .second).1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .secondSecond)) basis.second.2.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .secondSecond comparisonCells (by decide))]
      exact (rep .second).2.1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .secondThird)) basis.second.2.2
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .secondThird comparisonCells (by decide))]
      exact (rep .second).2.2
  | third =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .thirdFirst)) basis.third.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .thirdFirst comparisonCells (by decide))]
      exact (rep .third).1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .thirdSecond)) basis.third.2.1
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .thirdSecond comparisonCells (by decide))]
      exact (rep .third).2.1
    · change RawSignedRepresents ((LatticeLovasz.secondLovaszStore refs.lovasz store).read
        (LatticeMetricMachine.basisCellInput refs.basis .thirdThird)) basis.third.2.2
      rw [comparison_frame refs _ _
        (basis_avoids refs separation .thirdThird comparisonCells (by decide))]
      exact (rep .third).2.2
private theorem swap_first (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeArithmetic.PointRawRepresents
      (LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store)
      refs.basis.first basis.first := by
  refine ⟨?_, ?_, ?_⟩
  · change RawSignedRepresents
      ((LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstFirst)) basis.first.1
    rw [swap_frame refs _ _ (basis_avoids refs separation .firstFirst swapCells (by decide))]
    exact (rep .first).1
  · change RawSignedRepresents
      ((LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstSecond)) basis.first.2.1
    rw [swap_frame refs _ _ (basis_avoids refs separation .firstSecond swapCells (by decide))]
    exact (rep .first).2.1
  · change RawSignedRepresents
      ((LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store).read
        (LatticeMetricMachine.basisCellInput refs.basis .firstThird)) basis.first.2.2
    rw [swap_frame refs _ _ (basis_avoids refs separation .firstThird swapCells (by decide))]
    exact (rep .first).2.2

private theorem selectArm_basis (refs : Refs ctx width) (separation : Separation refs)
    (flag : CShape.Value .bit) (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents (selectArmStep refs flag store).1 refs.basis
      (if flag.toBool then basis else basis.swapSecondThird) := by
  cases flag with
  | bit flag =>
    cases flag
    · have swapped := LatticeSwap.pointSwap_correct _ _ _ separation.swap store
        basis.second basis.third (rep .second) (rep .third)
      intro row
      cases row with
      | first => exact swap_first refs separation store basis rep
      | second => exact swapped.1
      | third => exact swapped.2
    · exact rep

/-- The actual stored decision selects exactly the original pure second-Lovasz basis result. -/
theorem select_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis)
    (decision : (store.read (writeInput refs.lovasz.passes)).toBool = basis.secondLovasz) :
    LatticeMetricMachine.BasisRawRepresents (selectStep refs store).1 refs.basis
      (branchResult basis) := by
  have result := selectArm_basis refs separation
    (store.read (writeInput refs.lovasz.passes)) store basis rep
  change LatticeMetricMachine.BasisRawRepresents
    (selectArmStep refs (store.read (writeInput refs.lovasz.passes)) store).1 refs.basis _
  simpa only [decision, branchResult] using result

/-- Original pure basis result, actual retained decision and complete caller read frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.basis (branchResult basis)
  passes : (after.read (writeInput refs.lovasz.passes)).toBool = basis.secondLovasz
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    FrameAvoids refs mutableCells other → after.read other = before.read other

/-- Actual second-Lovasz comparison and its selected exchange realize the original contract. -/
theorem branchInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    Outcome refs store (branchStep refs store).1 basis := by
  have compared := comparison_basis refs separation store basis initial.basisRep
  have decision := LatticeLovasz.secondLovaszInto_matches_rawAreas refs.lovasz separation.lovasz
    store _ _ initial.area12 initial.area13 fits.firstFits fits.twiceSecondFits
  refine ⟨select_basis refs separation _ basis compared decision, ?_,
    branchInto_callerFrame refs store⟩
  change ((selectStep refs (LatticeLovasz.secondLovaszStore refs.lovasz store)).1.read
    (writeInput refs.lovasz.passes)).toBool = _
  rw [select_passes refs separation]
  exact decision

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
