/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.State.Workspace.Layout

/-!
# Persistent pair-state component views

This module maps the 25 physical state cells into the two terminal decoders,
the shared raw basis and target, the fixed-fuel machine state, and the saved
target.  It deliberately leaves all phase-local scratch references to later
layout layers.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairStateWorkspaceViews

open ClassicalRoutines

noncomputable section

namespace Layout

/-- Abbreviation for the local cell interface. -/
abbrev Cell := LatticePairStateWorkspaceLayout.Cell

/-- Abbreviation for the local width interface. -/
abbrev Width (N : Nat) := LatticePairStateWorkspaceLayout.Width N

/-- Abbreviation for the local cells interface. -/
abbrev Cells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  LatticePairStateWorkspaceLayout.Cells ctx N

/-- Abbreviation for the local cell ref interface. -/
abbrev cellRef {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Cells ctx N) (cell : Cell) :=
  LatticePairStateWorkspaceLayout.cellRef cells cell

end Layout

/-- First terminal decoder over the first four persistent cells. -/
def firstDecoderRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (input : CInputRef ctx (.bits (measurementBits N))) :
    BatchMachine.Refs ctx N where
  input := input
  full := Layout.cellRef cells .firstFull
  fullRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .firstFull)
  scratch := Layout.cellRef cells .firstScratch
  scratchRole := LatticePairStateWorkspaceLayout.cellRef_role cells .firstScratch
  j := Layout.cellRef cells .firstJ
  jRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .firstJ)
  k := Layout.cellRef cells .firstK
  kRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .firstK)

/-- Second terminal decoder over the second four persistent cells. -/
def secondDecoderRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) (input : CInputRef ctx (.bits (measurementBits N))) :
    BatchMachine.Refs ctx N where
  input := input
  full := Layout.cellRef cells .secondFull
  fullRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .secondFull)
  scratch := Layout.cellRef cells .secondScratch
  scratchRole := LatticePairStateWorkspaceLayout.cellRef_role cells .secondScratch
  j := Layout.cellRef cells .secondJ
  jRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .secondJ)
  k := Layout.cellRef cells .secondK
  kRole := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .secondK)

/-- The two terminal decoders sharing the persistent pair allocation. -/
def pairRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N)
    (firstInput secondInput : CInputRef ctx (.bits (measurementBits N))) :
    BatchMachine.PairRefs ctx N where
  first := firstDecoderRefs cells firstInput
  second := secondDecoderRefs cells secondInput

/-- Twelve raw wide cells shared by the initializer, driver, and target loader. -/
def rawRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeLoading.RawOutputRefs ctx (Layout.Width N) where
  b11 := Layout.cellRef cells .basis11
  b11Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis11)
  b12 := Layout.cellRef cells .basis12
  b12Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis12)
  b13 := Layout.cellRef cells .basis13
  b13Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis13)
  b21 := Layout.cellRef cells .basis21
  b21Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis21)
  b22 := Layout.cellRef cells .basis22
  b22Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis22)
  b23 := Layout.cellRef cells .basis23
  b23Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis23)
  b31 := Layout.cellRef cells .basis31
  b31Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis31)
  b32 := Layout.cellRef cells .basis32
  b32Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis32)
  b33 := Layout.cellRef cells .basis33
  b33Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .basis33)
  t1 := Layout.cellRef cells .targetFirst
  t1Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .targetFirst)
  t2 := Layout.cellRef cells .targetSecond
  t2Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .targetSecond)
  t3 := Layout.cellRef cells .targetThird
  t3Writable := Or.inl (LatticePairStateWorkspaceLayout.cellRef_role cells .targetThird)

/-- Workspace-role witnesses for all twelve raw cells. -/
theorem rawRoles {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeRepresentation.WorkspaceRoles (rawRefs cells) where
  b11 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis11
  b12 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis12
  b13 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis13
  b21 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis21
  b22 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis22
  b23 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis23
  b31 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis31
  b32 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis32
  b33 := LatticePairStateWorkspaceLayout.cellRef_role cells .basis33
  t1 := LatticePairStateWorkspaceLayout.cellRef_role cells .targetFirst
  t2 := LatticePairStateWorkspaceLayout.cellRef_role cells .targetSecond
  t3 := LatticePairStateWorkspaceLayout.cellRef_role cells .targetThird

/-- The first nine raw cells viewed as the mutable LLL basis. -/
def basisRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.BasisRefs ctx (Layout.Width N) :=
  LatticeRepresentation.basisRefs (rawRefs cells) (rawRoles cells)

/-- The final three raw cells viewed as the mutable centered target. -/
def targetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) :=
  LatticeRepresentation.targetRefs (rawRefs cells) (rawRoles cells)

/-- Mutable fixed-fuel basis plus its two phase latches. -/
def machineRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.MachineRefs ctx (Layout.Width N) where
  basis := basisRefs cells
  secondPhase := Layout.cellRef cells .secondPhase
  secondPhaseRole := LatticePairStateWorkspaceLayout.cellRef_role cells .secondPhase
  done := Layout.cellRef cells .done
  doneRole := LatticePairStateWorkspaceLayout.cellRef_role cells .done

/-- Caller-owned copy of the original centered target. -/
def savedTargetRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : Layout.Cells ctx N) : LatticeState.PointRefs ctx (Layout.Width N) where
  first := Layout.cellRef cells .savedTargetFirst
  firstRole := LatticePairStateWorkspaceLayout.cellRef_role cells .savedTargetFirst
  second := Layout.cellRef cells .savedTargetSecond
  secondRole := LatticePairStateWorkspaceLayout.cellRef_role cells .savedTargetSecond
  third := Layout.cellRef cells .savedTargetThird
  thirdRole := LatticePairStateWorkspaceLayout.cellRef_role cells .savedTargetThird

end

end LatticePairStateWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
