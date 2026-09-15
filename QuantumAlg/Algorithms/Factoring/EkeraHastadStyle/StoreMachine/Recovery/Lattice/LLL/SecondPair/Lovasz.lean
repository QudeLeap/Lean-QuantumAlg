/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz.Layout

/-!
# Actual second-pair Lovasz selection

The actual comparison writes its Boolean result to the supplied register.
That stored result selects identity on a pass and the complete row swap on a
failure, in the same actual circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- A pass keeps the basis; a failure exchanges the second and third rows. -/
def selectArm (refs : Refs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit true => .id ctx
  | .bit false => LatticeSwap.pointSwap refs.basis.second refs.basis.third refs.swapScratch

/-- Actual store and path of the selected identity or nine-copy exchange. -/
def selectArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (selectArm refs flag).Path :=
  match flag with
  | .bit true => (store, ())
  | .bit false =>
      (LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store,
        (((), ((), ())), ((), ((), ())), ((), ((), ()))))

/-- Read the actual Lovasz bit before choosing the executed row-exchange arm. -/
def selectInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.lovasz.passes) (selectArm refs)

/-- The actual selected store and the actual observed branch path. -/
def selectStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (selectInto refs).Path :=
  let chosen := selectArmStep refs (store.read (writeInput refs.lovasz.passes)) store
  (chosen.1, ⟨store.read (writeInput refs.lovasz.passes), chosen.2⟩)

private theorem selectArm_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (selectArm refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((selectArmStep refs flag entry.1).1, (entry.2, (selectArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (LatticeSwap.pointSwap_execute _ _ _ Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _

/-- Full actual selection uses the stored flag and preserves complete quantum-reference blocks. -/
theorem selectInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (selectInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((selectStep refs entry.1).1, (entry.2, (selectStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (selectArm_execute refs) Reference state

/-- Compute the actual second Lovasz decision and then execute its stored selection. -/
def branchInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (LatticeLovasz.secondLovaszInto refs.lovasz) (selectInto refs)

/-- The actual compared store feeds the actual row-selection branch. -/
def branchStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (branchInto refs).Path :=
  let compared := LatticeLovasz.secondLovaszStore refs.lovasz store
  let selected := selectStep refs compared
  (selected.1, (((), ((), ())), selected.2))

/-- The actual decision and selection compose chronologically in the full interpreter. -/
theorem branchInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (branchInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((branchStep refs entry.1).1, (entry.2, (branchStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeLovasz.secondLovaszInto refs.lovasz) (selectInto refs)
    (fun store => (LatticeLovasz.secondLovaszStore refs.lovasz store, ((), ((), ()))))
    (selectStep refs) (by
      intro Reference History _ state
      refine (LatticeLovasz.secondLovaszInto_execute refs.lovasz
        Reference state).trans ?_
      congr 1
      exact Subsingleton.elim _ _) (selectInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
