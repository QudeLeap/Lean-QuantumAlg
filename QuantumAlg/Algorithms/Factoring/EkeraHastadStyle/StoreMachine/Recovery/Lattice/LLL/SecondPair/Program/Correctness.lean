/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program.Frame

/-!
# Complete actual second-pair correctness

The two actual rounded quotients update the third row. Both areas are then
computed from that actual reduced basis, and the stored comparison selects the
actual row exchange. All six original outputs survive in the final store.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual prefix supplies the original input domain of the final direction reduction. -/
lemma post_initial {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    (basis : NumberTheory.IntegerBasis3) (initial : Initial refs store basis)
    (result : LatticeSecondPairMachine.Outcome refs.machine store
      (LatticeSecondPairMachine.secondPairPrefixStep (model := model) refs.machine store).1
      basis) :
    LatticeSecondPairPostReduction.Initial refs.post
      (LatticeSecondPairMachine.secondPairPrefixStep (model := model) refs.machine store).1
      (LatticeSecondPairMachine.secondPairPrefixResult basis) := by
  constructor
  · rw [refs.postMachine]
    exact result.basisRep
  · rw [refs.postMachine, result.firstNorm]
    exact initial.firstNorm

/-- Both actual rounded quotients survive together with the fully size-reduced basis. -/
lemma sizeReduction_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    LatticeMetricMachine.BasisRawRepresents
      (sizeReductionStep (model := model) refs store).1 refs.machine.basis
        (secondPairReducedResult basis) ∧
      RawSignedRepresents ((sizeReductionStep (model := model) refs store).1.read
        (LatticeArithmetic.writeInput refs.machine.division32.output))
          basis.sizeReduceSecondPair.2.1 ∧
      RawSignedRepresents ((sizeReductionStep (model := model) refs store).1.read
        (LatticeArithmetic.writeInput refs.machine.division31.output))
          basis.sizeReduceSecondPair.2.2 := by
  have first := LatticeSecondPairMachine.secondPairPrefixInto_correct refs.machine
    separation.prefixPhase store basis initial fits.prefixPhase
  have second := LatticeSecondPairPostReduction.postReductionInto_correct refs.post separation.post
    _ _ (post_initial refs store basis initial first) fits.post
  refine ⟨?_, ?_, ?_⟩
  · have represented := second.basisRep
    rw [refs.postMachine] at represented
    exact represented
  · change RawSignedRepresents ((LatticeSecondPairPostReduction.postReductionStep refs.post
      (LatticeSecondPairMachine.secondPairPrefixStep (model := model)
        refs.machine store).1).1.read
        (LatticeArithmetic.writeInput refs.machine.division32.output)) _
    rw [post_frame refs _ _ (write_avoids refs separation refs.machine.division32.output
      (.transition (.division32 .output)) rfl postCells (by decide))]
    exact first.coefficient
  · have coefficient := second.coefficient
    rw [refs.postMachine] at coefficient
    exact coefficient

/-- The actual area-12 scratch writes leave every represented basis coordinate intact. -/
lemma area12_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.second
        refs.area12 store) refs.machine.basis basis := by
  apply basis_raw_of_frame refs separation basis area12Cells rep (area12_frame refs store)
  intro cell
  cases cell <;> decide

/-- The actual area-13 scratch writes leave every represented basis coordinate intact. -/
lemma area13_basis (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeMetricMachine.BasisRawRepresents
      (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.third
        refs.area13 store) refs.machine.basis basis := by
  apply basis_raw_of_frame refs separation basis area13Cells rep (area13_frame refs store)
  intro cell
  cases cell <;> decide

/-- The two actual area refreshes supply the original branch input, retaining the first area. -/
lemma branch_initial (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis) :
    LatticeSecondLovaszBranch.Initial refs.branch
      (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.third refs.area13
        (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.second
          refs.area12 store)) basis := by
  have first := LatticeAreaRefresh.refreshInto_correct _ _ _ separation.area12Refresh store
    basis.first basis.second (rep .first) (rep .second)
  have firstBasis := area12_basis refs separation store basis rep
  have second := LatticeAreaRefresh.refreshInto_correct _ _ _ separation.area13Refresh _
    basis.first basis.third (firstBasis .first) (firstBasis .third)
  have secondBasis := area13_basis refs separation _ basis firstBasis
  refine ⟨?_, ?_, ?_⟩
  · rw [refs.branchBasis]
    exact secondBasis
  · rw [refs.branchArea12, area13_frame refs _ _
      (write_avoids refs separation refs.area12.area .area12Result rfl area13Cells (by decide))]
    exact first.1
  · rw [refs.branchArea13]
    exact second.1

/-- Both area outputs and the actual decision survive the selected second-row exchange. -/
structure AreaOutcome (refs : Refs ctx width) (after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.machine.basis
    (LatticeSecondLovaszBranch.branchResult basis)
  area12 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput refs.area12.area))
    (NumberTheory.integerPointAreaSquared basis.first basis.second : Int)
  area13 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput refs.area13.area))
    (NumberTheory.integerPointAreaSquared basis.first basis.third : Int)
  passes : (after.read (LatticeArithmetic.writeInput refs.branch.lovasz.passes)).toBool =
    basis.secondLovasz

/-- Actual area computations and the selected branch realize all original suffix outputs. -/
lemma areaBranch_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (rep : LatticeMetricMachine.BasisRawRepresents store refs.machine.basis basis)
    (fits : LatticeSecondLovaszBranch.Fits width basis) :
    AreaOutcome refs (areaBranchStep (model := model) refs store).1 basis := by
  have initial := branch_initial refs separation store basis rep
  have selected := LatticeSecondLovaszBranch.branchInto_correct refs.branch separation.branch
    _ basis initial fits
  refine ⟨?_, ?_, ?_, selected.passes⟩
  · have represented := selected.basisRep
    rw [refs.branchBasis] at represented
    exact represented
  · change RawSignedRepresents
      ((LatticeSecondLovaszBranch.branchStep (model := model) refs.branch _).1.read
      (LatticeArithmetic.writeInput refs.area12.area)) _
    rw [branch_frame refs _ _
      (write_avoids refs separation refs.area12.area .area12Result rfl branchCells (by decide))]
    have area := initial.area12
    rw [refs.branchArea12] at area
    exact area
  · change RawSignedRepresents
      ((LatticeSecondLovaszBranch.branchStep (model := model) refs.branch _).1.read
      (LatticeArithmetic.writeInput refs.area13.area)) _
    rw [branch_frame refs _ _
      (write_avoids refs separation refs.area13.area .area13Result rfl branchCells (by decide))]
    have area := initial.area13
    rw [refs.branchArea13] at area
    exact area

/-- Original numeric outputs and the full caller frame of the actual complete transition. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  coefficient32 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput
    refs.machine.division32.output))
    basis.sizeReduceSecondPair.2.1
  coefficient31 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput
    refs.machine.division31.output))
    basis.sizeReduceSecondPair.2.2
  area12 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput refs.area12.area))
    (NumberTheory.integerPointAreaSquared basis.first basis.second : Int)
  area13 : RawSignedRepresents (after.read (LatticeArithmetic.writeInput refs.area13.area))
    (NumberTheory.integerPointAreaSquared (secondPairReducedResult basis).first
      (secondPairReducedResult basis).third : Int)
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.machine.basis
    (secondPairResult basis)
  passes : (after.read (LatticeArithmetic.writeInput refs.branch.lovasz.passes)).toBool =
    (secondPairReducedResult basis).secondLovasz
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    FrameAvoids refs mutableCells other → after.read other = before.read other

/-- The complete actual transition realizes every original output on the original input domain. -/
lemma secondPairInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    Outcome refs store (secondPairStep (model := model) refs store).1 basis := by
  have reduced := sizeReduction_correct refs separation store basis initial fits
  have selected := areaBranch_correct refs separation _ _ reduced.1 fits.branch
  refine ⟨?_, ?_, selected.area12, selected.area13, selected.basisRep, selected.passes,
    secondPairInto_callerFrame refs store⟩
  · change RawSignedRepresents
      ((areaBranchStep (model := model) refs
        (sizeReductionStep (model := model) refs store).1).1.read
      (LatticeArithmetic.writeInput refs.machine.division32.output)) _
    rw [areaBranch_frame refs _ _ (write_avoids refs separation refs.machine.division32.output
      (.transition (.division32 .output)) rfl areaBranchCells (by decide))]
    exact reduced.2.1
  · change RawSignedRepresents
      ((areaBranchStep (model := model) refs
        (sizeReductionStep (model := model) refs store).1).1.read
      (LatticeArithmetic.writeInput refs.machine.division31.output)) _
    rw [areaBranch_frame refs _ _ (write_avoids refs separation refs.machine.division31.output
      (.transition (.division31 .output)) rfl areaBranchCells (by decide))]
    exact reduced.2.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
