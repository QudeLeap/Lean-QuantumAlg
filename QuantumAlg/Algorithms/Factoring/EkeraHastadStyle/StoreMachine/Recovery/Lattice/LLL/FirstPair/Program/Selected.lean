/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Frame

/-!
# Actual first-pair branch correctness

The stored comparison bit selects the actual identity or row exchange. The
original pure basis, decision bit and refreshed norm survive the selected arm.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Comparison preserves all actual basis coordinates outside its two writes. -/
theorem comparison_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeLovasz.firstLovaszStore refs.metric refs.lovasz store) refs.basis basis := by
  intro row
  apply row_raw_of_frame refs separation row _ comparisonCells (rep row)
    (comparison_frame refs store)
  intro cell member
  cases cell <;> decide

private theorem selectArm_basis {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (flag : CShape.Value .bit) (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (selectArmStep (model := model) refs flag store).1 refs.basis
      (if flag.toBool then basis else basis.swapFirstSecond) := by
  cases flag with
  | bit flag =>
    cases flag
    · have swapped := LatticeSwap.pointSwap_correct _ _ _ separation.swap store
        basis.first basis.second (rep .first) (rep .second)
      intro row
      cases row with
      | first => exact swapped.1
      | second => exact swapped.2
      | third =>
        apply row_raw_of_frame refs separation .third _ swapCells (rep .third)
          (swap_frame refs store)
        intro cell member
        cases cell <;> simp_all [rowCells, basisTransitionCell, swapCells]
    · exact rep

/-- The actual stored decision selects exactly the original pure Lovasz basis result. -/
theorem select_basis {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis)
    (decision : (store.read (writeInput refs.lovasz.passes)).toBool = basis.firstLovasz) :
    LatticeMetricMachine.BasisRawRepresents (selectStep (model := model) refs store).1 refs.basis
      (lovaszBranchResult basis) := by
  have result := selectArm_basis refs separation
    (store.read (writeInput refs.lovasz.passes)) store basis rep
  change LatticeMetricMachine.BasisRawRepresents
    (selectArmStep (model := model) refs
      (store.read (writeInput refs.lovasz.passes)) store).1 refs.basis _
  simpa only [decision, lovaszBranchResult] using result

/-- Both actual selected arms preserve the comparison result bit exactly. -/
theorem select_passes {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (selectStep (model := model) refs store).1.read (writeInput refs.lovasz.passes) =
      store.read (writeInput refs.lovasz.passes) := by
  apply select_frame
  intro cell member
  have different : cell ≠ .passes := by
    intro equal
    subst cell
    simp [swapCells] at member
  have keyNe := separation.phase.cellKey_ne cell .passes different
  simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton, cellKey] using keyNe

/-- The actual comparison and selected exchange retain the refreshed second norm word. -/
theorem lovaszBranch_g22 {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) :
    (lovaszBranchStep (model := model) refs store).1.read (writeInput refs.metric.g22) =
      store.read (writeInput refs.metric.g22) := by
  change (selectStep (model := model) refs
    (LatticeLovasz.firstLovaszStore refs.metric refs.lovasz store)).1.read
    (writeInput (LatticeMetricMachine.metricCellRef refs.metric .g22)) = _
  rw [select_frame refs _ _ (metric_avoids refs separation .g22 swapCells (by decide)),
    comparison_frame refs _ _ (metric_avoids refs separation .g22 comparisonCells (by decide))]
  rfl

/-- Actual bounded norm comparison followed by its actual selected row exchange is correct. -/
theorem lovaszBranch_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis)
    (firstNorm : RawSignedRepresents (store.read (writeInput refs.metric.g11))
      (NumberTheory.integerPointSquaredNorm basis.first : Int))
    (secondNorm : RawSignedRepresents (store.read (writeInput refs.metric.g22))
      (NumberTheory.integerPointSquaredNorm basis.second : Int))
    (firstFits : NumberTheory.integerPointSquaredNorm basis.first < CShape.wordModulus width)
    (twiceSecondFits : 2 * NumberTheory.integerPointSquaredNorm basis.second <
      CShape.wordModulus width) :
    LatticeMetricMachine.BasisRawRepresents
      (lovaszBranchStep (model := model) refs store).1 refs.basis
        (lovaszBranchResult basis) ∧
      ((lovaszBranchStep (model := model) refs store).1.read
        (writeInput refs.lovasz.passes)).toBool =
        basis.firstLovasz := by
  have decision := LatticeLovasz.firstLovaszInto_matches_rawNorms _ _ separation.lovasz store
    _ _ firstNorm secondNorm firstFits twiceSecondFits
  have compared := comparison_basis refs separation store basis rep
  refine ⟨select_basis refs separation _ basis compared decision, ?_⟩
  change ((selectStep (model := model) refs
    (LatticeLovasz.firstLovaszStore refs.metric refs.lovasz store)).1.read
      (writeInput refs.lovasz.passes)).toBool = _
  rw [select_passes refs separation]
  exact decision

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
