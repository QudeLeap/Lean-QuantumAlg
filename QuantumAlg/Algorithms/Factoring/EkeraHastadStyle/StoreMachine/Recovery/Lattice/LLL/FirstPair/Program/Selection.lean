/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program.Layout

/-!
# Actual first-pair Lovasz selection

The actual comparison writes its Boolean result to the supplied register.
That stored result selects identity on a pass and the complete row swap on a
failure, in the same actual circuit interpreter.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual passing arm keeps the basis; the failing arm exchanges the first two rows. -/
def selectArm {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) :
    CShape.Value .bit → Circuit model ctx ctx
  | .bit true => .id ctx
  | .bit false => LatticeSwap.pointSwap refs.basis.first refs.basis.second refs.swapScratch

/-- Actual store and path of the selected identity or nine-copy exchange. -/
def selectArmStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (selectArm (model := model) refs flag).Path :=
  match flag with
  | .bit true => (store, ())
  | .bit false =>
      LatticeSwap.pointSwapStep (model := model)
        refs.basis.first refs.basis.second refs.swapScratch store

/-- Read the actual Lovasz bit before choosing the executed row-exchange arm. -/
def selectInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (writeInput refs.lovasz.passes) (selectArm (model := model) refs)

/-- The actual selected store and the actual observed branch path. -/
def selectStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (selectInto (model := model) refs).Path :=
  let chosen := selectArmStep (model := model) refs
    (store.read (writeInput refs.lovasz.passes)) store
  (chosen.1, ⟨store.read (writeInput refs.lovasz.passes), chosen.2⟩)

private theorem selectArm_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectArm (model := model) refs flag).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := selectArmStep (model := model) refs flag entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · exact LatticeSwap.pointSwap_execute _ _ _ Reference state
    · refine (Circuit.execute_id_mapClassical Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Full actual selection uses the stored flag and preserves complete quantum-reference blocks. -/
theorem selectInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (selectInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := selectStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical (writeInput refs.lovasz.passes)
    (selectArm (model := model) refs)
    (fun flag before =>
      let actual := selectArmStep (model := model) refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      selectArm_execute refs flag reference current) Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Compute the actual first Lovasz decision and then execute its stored selection. -/
def lovaszBranchInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeLovasz.firstLovaszInto (model := model) refs.metric refs.lovasz)
    (selectInto (model := model) refs)

/-- The actual compared store feeds the actual row-selection branch. -/
def lovaszBranchStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (lovaszBranchInto (model := model) refs).Path :=
  let compared := ClassicalRoutines.Comparison.Doubled.executionStep (model := model)
    (LatticeLovasz.firstComparisonRefs refs.metric refs.lovasz) store
  let selected := selectStep (model := model) refs compared.1
  (selected.1, (compared.2, selected.2))

/-- The actual decision and selection compose chronologically in the full interpreter. -/
theorem lovaszBranchInto_execute {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (lovaszBranchInto (model := model) refs).execute Reference state =
      state.mapClassical (fun entry =>
        let actual := lovaszBranchStep (model := model) refs entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (LatticeLovasz.firstLovaszInto (model := model) refs.metric refs.lovasz)
    (selectInto (model := model) refs)
    (fun before =>
      let actual := ClassicalRoutines.Comparison.Doubled.executionStep (model := model)
        (LatticeLovasz.firstComparisonRefs refs.metric refs.lovasz) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := selectStep (model := model) refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      LatticeLovasz.firstLovaszInto_execute refs.metric refs.lovasz reference current)
    (fun reference _history _ current => selectInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
