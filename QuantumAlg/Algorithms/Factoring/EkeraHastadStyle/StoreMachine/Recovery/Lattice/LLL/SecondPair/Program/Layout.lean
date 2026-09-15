/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Gram.Area

/-!
# Original complete second-pair layout and domain

The five original phase packages share their actual declared identities.
Their numeric conditions are precisely the original prefix, final reduction
and second-Lovasz conditions on the corresponding pure basis values.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

/-- Caller-owned packages for the complete second-pair transition. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Nested references for the machine stage. -/
  machine : LatticeSecondPairMachine.Refs ctx width
  /-- Nested references for the post stage. -/
  post : LatticeSecondPairPostReduction.Refs ctx width
  /-- Nested references for the area 12 stage. -/
  area12 : LatticeAreaRefresh.Refs ctx width
  /-- Nested references for the area 13 stage. -/
  area13 : LatticeAreaRefresh.Refs ctx width
  /-- Nested references for the branch stage. -/
  branch : LatticeSecondLovaszBranch.Refs ctx width
  postMachine : post.machine = machine
  branchBasis : branch.basis = machine.basis
  branchArea12 : branch.lovasz.area12 = LatticeArithmetic.writeInput area12.area
  branchArea13 : branch.lovasz.area13 = LatticeArithmetic.writeInput area13.area

/-- Every independently addressed cell used by the complete transition. -/
inductive Cell where
  | transition (cell : LatticeSecondPairMachine.TransitionCell)
  | area12ProductLeft | area12ProductRight
  | area12CrossFirst | area12CrossSecond | area12CrossThird
  | area12Result | area12NormProduct
  | area13ProductLeft | area13ProductRight
  | area13CrossFirst | area13CrossSecond | area13CrossThird
  | area13Result | area13NormProduct
  | lovaszDoubled | lovaszPasses | swapScratch
deriving DecidableEq

/-- Resolve each complete-transition cell to its concrete caller-owned key. -/
def cellKey {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Cell → StorageKey
  | .transition cell => LatticeSecondPairMachine.cellKey refs.machine cell
  | .area12ProductLeft => refs.area12.productLeft.toCStorageRef.key
  | .area12ProductRight => refs.area12.productRight.toCStorageRef.key
  | .area12CrossFirst => refs.area12.cross.first.toCStorageRef.key
  | .area12CrossSecond => refs.area12.cross.second.toCStorageRef.key
  | .area12CrossThird => refs.area12.cross.third.toCStorageRef.key
  | .area12Result => refs.area12.area.toCStorageRef.key
  | .area12NormProduct => refs.area12.normProduct.toCStorageRef.key
  | .area13ProductLeft => refs.area13.productLeft.toCStorageRef.key
  | .area13ProductRight => refs.area13.productRight.toCStorageRef.key
  | .area13CrossFirst => refs.area13.cross.first.toCStorageRef.key
  | .area13CrossSecond => refs.area13.cross.second.toCStorageRef.key
  | .area13CrossThird => refs.area13.cross.third.toCStorageRef.key
  | .area13Result => refs.area13.area.toCStorageRef.key
  | .area13NormProduct => refs.area13.normProduct.toCStorageRef.key
  | .lovaszDoubled => refs.branch.lovasz.doubled.toCStorageRef.key
  | .lovaszPasses => refs.branch.lovasz.passes.toCStorageRef.key
  | .swapScratch => refs.branch.swapScratch.toCStorageRef.key

/-- Global key separation together with the local separation packages. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  keyInjective : Function.Injective (cellKey refs)
  prefixPhase : LatticeSecondPairMachine.Separation refs.machine
  post : LatticeSecondPairPostReduction.Separation refs.post
  area12Refresh : LatticeAreaRefresh.Separation refs.machine.basis.first
    refs.machine.basis.second refs.area12
  area13Refresh : LatticeAreaRefresh.Separation refs.machine.basis.first
    refs.machine.basis.third refs.area13
  branch : LatticeSecondLovaszBranch.Separation refs.branch

/-- The original second-pair size-reduced basis before its Lovasz decision. -/
def secondPairReducedResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  LatticeSecondPairPostReduction.postReductionResult
    (LatticeSecondPairMachine.secondPairPrefixResult basis)

/-- The original complete second-pair result, including its original Lovasz choice. -/
def secondPairResult (basis : NumberTheory.IntegerBasis3) : NumberTheory.IntegerBasis3 :=
  LatticeSecondLovaszBranch.branchResult (secondPairReducedResult basis)

/-- Exactly the original four representation facts at complete second-pair entry. -/
abbrev Initial {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) (store : Store ctx) (basis : NumberTheory.IntegerBasis3) : Prop :=
  LatticeSecondPairMachine.Initial refs.machine store basis

/-- The original numeric conditions, grouped by the corresponding original pure phase input. -/
structure Fits (width : Nat) (basis : NumberTheory.IntegerBasis3) : Prop where
  prefixPhase : LatticeSecondPairMachine.Fits width basis
  post : LatticeSecondPairPostReduction.Fits width
    (LatticeSecondPairMachine.secondPairPrefixResult basis)
  branch : LatticeSecondLovaszBranch.Fits width (secondPairReducedResult basis)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
