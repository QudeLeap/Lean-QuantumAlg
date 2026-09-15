/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Prefix
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Selected

/-!
# Complete actual first-pair correctness

The actual circuit reaches the original size-reduction and Lovasz result on
the original numerical domain, with no initial scratch or other Gram premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual final basis, actual retained decision and norm, and complete caller read frame. -/
structure Outcome (refs : Refs ctx width) (before after : Store ctx)
    (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents after refs.basis (firstPairResult basis)
  passes : (after.read (writeInput refs.lovasz.passes)).toBool =
    basis.sizeReduceFirstPair.1.firstLovasz
  secondNorm : RawSignedRepresents (after.read (writeInput refs.metric.g22))
    (NumberTheory.integerPointSquaredNorm basis.sizeReduceFirstPair.1.second : Int)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    FrameAvoids refs mutableCells other → after.read other = before.read other

/-- Complete actual first-pair execution realizes the original result without extra hypotheses. -/
theorem firstPairInto_correct (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) (basis : NumberTheory.IntegerBasis3)
    (initial : Initial refs store basis) (fits : Fits width basis) :
    Outcome refs store (firstPairStep refs store).1 basis := by
  have reduced := reductionPrefix_correct refs separation store basis initial fits
  have selected := lovaszBranch_correct refs separation (reductionPrefixStep refs store).1
    basis.sizeReduceFirstPair.1 reduced.1 reduced.2.1 reduced.2.2
    fits.firstFits fits.twiceSecondFits
  refine ⟨selected.1, selected.2, ?_, firstPairInto_callerFrame refs store⟩
  change RawSignedRepresents
    ((lovaszBranchStep refs (reductionPrefixStep refs store).1).1.read
      (writeInput refs.metric.g22)) _
  rw [lovaszBranch_g22 refs separation]
  exact reduced.2.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
