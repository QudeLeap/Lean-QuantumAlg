/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz.Decision
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Row.Swap.Resources

/-!
# Original second-Lovasz branch layout

The original twelve distinct mutable identities and four area-read exclusions
suffice for the actual comparison and conditional final-two-row exchange.
Area inputs may share basis cells, as allowed by the original contract.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned basis, second-Lovasz cells, and scratch for the failing swap. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the basis stage. -/
  basis : LatticeState.BasisRefs ctx width
  /-- Nested references for the lovasz stage. -/
  lovasz : LatticeLovasz.SecondLovaszRefs ctx width
  /-- Writable cell for the swap scratch value. -/
  swapScratch : CWriteRef ctx (LatticeState.RawSignedWordShape width)
  swapScratchRole : swapScratch.toCStorageRef.role = .workspace

/-- Every independently addressed cell touched by the branch. -/
inductive BranchCell where
  | b11 | b12 | b13 | b21 | b22 | b23 | b31 | b32 | b33
  | doubled | passes | swapScratch
deriving DecidableEq

/-- Resolve a branch cell to its concrete caller-owned storage key. -/
def cellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : BranchCell → StorageKey
  | .b11 => refs.basis.first.first.toCStorageRef.key
  | .b12 => refs.basis.first.second.toCStorageRef.key
  | .b13 => refs.basis.first.third.toCStorageRef.key
  | .b21 => refs.basis.second.first.toCStorageRef.key
  | .b22 => refs.basis.second.second.toCStorageRef.key
  | .b23 => refs.basis.second.third.toCStorageRef.key
  | .b31 => refs.basis.third.first.toCStorageRef.key
  | .b32 => refs.basis.third.second.toCStorageRef.key
  | .b33 => refs.basis.third.third.toCStorageRef.key
  | .doubled => refs.lovasz.doubled.toCStorageRef.key
  | .passes => refs.lovasz.passes.toCStorageRef.key
  | .swapScratch => refs.swapScratch.toCStorageRef.key

/-- Embed one named basis coordinate into the branch-wide cell naming. -/
def basisBranchCell : LatticeMetricMachine.BasisCell → BranchCell
  | .firstFirst => .b11
  | .firstSecond => .b12
  | .firstThird => .b13
  | .secondFirst => .b21
  | .secondSecond => .b22
  | .secondThird => .b23
  | .thirdFirst => .b31
  | .thirdSecond => .b32
  | .thirdThird => .b33

private def swapBranchCell : LatticeSwap.PointSwapCell → BranchCell
  | .leftFirst => .b21
  | .leftSecond => .b22
  | .leftThird => .b23
  | .rightFirst => .b31
  | .rightSecond => .b32
  | .rightThird => .b33
  | .scratch => .swapScratch

/-- All branch-owned keys are globally pairwise distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (cellKey refs)
  area12AvoidsDoubled : refs.lovasz.doubled.key ∉ refs.lovasz.area12.storageKeys
  area13AvoidsDoubled : refs.lovasz.doubled.key ∉ refs.lovasz.area13.storageKeys
  area12AvoidsPass : refs.lovasz.passes.key ∉ refs.lovasz.area12.storageKeys
  area13AvoidsPass : refs.lovasz.passes.key ∉ refs.lovasz.area13.storageKeys

/-- Different named branch cells resolve to different storage keys. -/
theorem Separation.cellKey_ne {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : Separation refs)
    (left right : BranchCell) (different : left ≠ right) :
    cellKey refs left ≠ cellKey refs right := by
  intro equal
  exact different (separation.keyInjective equal)

/-- The original branch separation supplies the scalar area's five actual exclusions. -/
theorem Separation.lovasz {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    {refs : Refs ctx width} (separation : Separation refs) :
    LatticeLovasz.SecondLovaszSeparation refs.lovasz := by
  refine ⟨separation.area12AvoidsDoubled, separation.area13AvoidsDoubled,
    separation.area12AvoidsPass, separation.area13AvoidsPass, ?_⟩
  change cellKey refs .passes ∉ [cellKey refs .doubled]
  simpa only [List.mem_singleton] using separation.cellKey_ne .passes .doubled (by decide)

private theorem pointSwapCellKey_eq {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (refs : Refs ctx width) (cell : LatticeSwap.PointSwapCell) :
    LatticeSwap.pointSwapCellKey refs.basis.second refs.basis.third refs.swapScratch cell =
      cellKey refs (swapBranchCell cell) := by
  cases cell <;> rfl

private theorem swapBranchCell_injective : Function.Injective swapBranchCell := by
  intro left right equal
  cases left <;> cases right <;> cases equal <;> rfl

/-- The original distinct branch cells supply the selected row exchange separation. -/
theorem Separation.swap {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} {refs : Refs ctx width} (separation : Separation refs) :
    LatticeSwap.PointSwapSeparation refs.basis.second refs.basis.third refs.swapScratch := by
  refine ⟨?_⟩
  intro left right equal
  apply swapBranchCell_injective
  apply separation.keyInjective
  calc
    cellKey refs (swapBranchCell left) =
        LatticeSwap.pointSwapCellKey refs.basis.second refs.basis.third refs.swapScratch left :=
      (pointSwapCellKey_eq refs left).symm
    _ = LatticeSwap.pointSwapCellKey refs.basis.second refs.basis.third refs.swapScratch right :=
      equal
    _ = cellKey refs (swapBranchCell right) := pointSwapCellKey_eq refs right

/-- The pure basis selected after the second Lovasz decision. -/
def branchResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  if basis.secondLovasz then basis else basis.swapSecondThird

/-- The original basis and area values read before the actual comparison. -/
structure Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) (basis : NumberTheory.IntegerBasis3) : Prop where
  basisRep : LatticeMetricMachine.BasisRawRepresents store refs.basis basis
  area12 : RawSignedRepresents (store.read refs.lovasz.area12)
    (NumberTheory.integerPointAreaSquared basis.first basis.second : Int)
  area13 : RawSignedRepresents (store.read refs.lovasz.area13)
    (NumberTheory.integerPointAreaSquared basis.first basis.third : Int)

/-- Exactly the original unsigned area capacity conditions. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  firstFits : NumberTheory.integerPointAreaSquared basis.first basis.second <
    CShape.wordModulus width
  twiceSecondFits : 2 * NumberTheory.integerPointAreaSquared basis.first basis.third <
    CShape.wordModulus width

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
