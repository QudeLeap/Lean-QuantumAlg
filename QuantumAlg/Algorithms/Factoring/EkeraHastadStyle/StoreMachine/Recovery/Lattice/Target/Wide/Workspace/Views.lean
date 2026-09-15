/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Workspace.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Views

/-!
# Wide-target scratch component views

This module combines the eight phase-local cells with the persistent decoded
pair and raw target cells.  The resulting view is the exact caller-owned
reference package consumed by `LatticeWideTargetMachine`.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeWideTargetWorkspaceViews

open ClassicalRoutines

noncomputable section

namespace Scratch

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticeWideTargetWorkspaceLayout.Cell

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) := LatticeWideTargetWorkspaceLayout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticeWideTargetWorkspaceLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticeWideTargetWorkspaceLayout.cellRef cells cell

end Scratch

namespace State

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticePairStateWorkspaceViews.Layout.Cells ctx N

end State

/-- The modulus word is the persistent `2^(ell+m)` basis coordinate. -/
def modulusInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) : CInputRef ctx (.unsignedWord (Scratch.Width N)) :=
  LatticeLoading.writeInput (LatticePairStateWorkspaceViews.rawRefs state).b21

/-- First decoded `k` word and its wide preimage output. -/
def firstPreimageRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) (pair : BatchMachine.PairRefs ctx N) :
    LatticeWideTargetMachine.PreimageRefs ctx (shortLogBits N) (tradeoffBits N)
      (Scratch.Width N) where
  k := LatticeLoading.writeInput pair.first.k
  scaled := Scratch.cellRef scratch .firstScaled
  scaledWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .firstScaled)

/-- Second decoded `k` word and its wide preimage output. -/
def secondPreimageRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (scratch : Scratch.Cells ctx N) (pair : BatchMachine.PairRefs ctx N) :
    LatticeWideTargetMachine.PreimageRefs ctx (shortLogBits N) (tradeoffBits N)
      (Scratch.Width N) where
  k := LatticeLoading.writeInput pair.second.k
  scaled := Scratch.cellRef scratch .secondScaled
  scaledWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .secondScaled)

/-- First centered-coordinate loader backed by the persistent first target. -/
def firstTargetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) :
    LatticeTarget.Refs ctx (Scratch.Width N) where
  a := LatticeWideTargetMachine.writeInput (firstPreimageRefs scratch pair).scaled
  modulus := modulusInput state
  scratch := Scratch.cellRef scratch .firstScratch
  scratchWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .firstScratch)
  isZero := Scratch.cellRef scratch .firstIsZero
  isZeroWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .firstIsZero)
  belowHalf := Scratch.cellRef scratch .firstBelowHalf
  belowHalfWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .firstBelowHalf)
  output := (LatticePairStateWorkspaceViews.targetRefs state).first
  outputWritable := Or.inl
    (LatticePairStateWorkspaceLayout.cellRef_role state .targetFirst)

/-- Second centered-coordinate loader backed by the persistent second target. -/
def secondTargetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) :
    LatticeTarget.Refs ctx (Scratch.Width N) where
  a := LatticeWideTargetMachine.writeInput (secondPreimageRefs scratch pair).scaled
  modulus := modulusInput state
  scratch := Scratch.cellRef scratch .secondScratch
  scratchWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .secondScratch)
  isZero := Scratch.cellRef scratch .secondIsZero
  isZeroWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .secondIsZero)
  belowHalf := Scratch.cellRef scratch .secondBelowHalf
  belowHalfWritable := Or.inl
    (LatticeWideTargetWorkspaceLayout.cellRef_role scratch .secondBelowHalf)
  output := (LatticePairStateWorkspaceViews.targetRefs state).second
  outputWritable := Or.inl
    (LatticePairStateWorkspaceLayout.cellRef_role state .targetSecond)

/-- Both centered loaders share the persistent target point. -/
def targetPointRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) :
    LatticeTargetPoint.Refs ctx (Scratch.Width N) where
  first := firstTargetRefs state scratch pair
  second := secondTargetRefs state scratch pair
  point := LatticePairStateWorkspaceViews.targetRefs state
  firstOutput := rfl
  secondOutput := rfl

/-- Exact wide-target package over the decoded pair and physical cells. -/
def targetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (state : State.Cells ctx N) (scratch : Scratch.Cells ctx N)
    (pair : BatchMachine.PairRefs ctx N) :
    LatticeWideTargetMachine.Refs ctx (shortLogBits N) (tradeoffBits N)
      (Scratch.Width N) where
  first := firstPreimageRefs scratch pair
  second := secondPreimageRefs scratch pair
  target := targetPointRefs state scratch pair
  modulus := modulusInput state
  firstInput := rfl
  secondInput := rfl
  firstModulus := rfl
  secondModulus := rfl

end

end LatticeWideTargetWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
