/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Lovasz

/-!
# Actual second-Lovasz write frames

The original branch identities isolate the comparison and final-two-row swap
writes. Both actual outcomes retain every other caller read, including the
first basis row and the stored decision bit.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch

open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two actual comparison writes. -/
def comparisonCells : List BranchCell := [.doubled, .passes]

/-- The six exchanged words and retained scratch used by the actual failing arm. -/
def swapCells : List BranchCell := [.b21, .b22, .b23, .b31, .b32, .b33, .swapScratch]

/-- Every possible actual write of the complete second-Lovasz branch. -/
def mutableCells : List BranchCell := comparisonCells ++ swapCells

/-- A caller read avoids every named mutable identity in the supplied footprint. -/
def FrameAvoids (refs : Refs ctx width) (cells : List BranchCell)
    {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ cell ∈ cells, cellKey refs cell ∉ other.storageKeys

/-- Original distinct branch identities provide the caller frame for each named basis read. -/
lemma basis_avoids (refs : Refs ctx width) (separation : Separation refs)
    (cell : LatticeMetricMachine.BasisCell) (cells : List BranchCell)
    (absent : basisBranchCell cell ∉ cells) :
    FrameAvoids refs cells (LatticeMetricMachine.basisCellInput refs.basis cell) := by
  intro target member
  have different : target ≠ basisBranchCell cell := fun equal => absent (equal ▸ member)
  have keyNe := separation.cellKey_ne target (basisBranchCell cell) different
  cases cell <;>
    simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
      CInputRef.storageKeys, List.mem_singleton, basisBranchCell, cellKey] using keyNe

/-- Actual comparison preserves all caller reads outside its two written cells. -/
lemma comparison_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs comparisonCells other) :
    (LatticeLovasz.secondLovaszStore refs.lovasz store).read other = store.read other :=
  LatticeLovasz.secondLovaszInto_callerFrame _ _ other
    (avoids .doubled (by decide)) (avoids .passes (by decide))

/-- Actual exchange of the final two rows preserves every read outside its seven written cells. -/
lemma swap_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (LatticeSwap.pointSwapStore refs.basis.second refs.basis.third refs.swapScratch store).read
      other = store.read other := by
  apply LatticeSwap.pointSwap_callerFrame _ _ _ _ other
  intro cell
  cases cell
  · exact avoids .b21 (by decide)
  · exact avoids .b22 (by decide)
  · exact avoids .b23 (by decide)
  · exact avoids .b31 (by decide)
  · exact avoids .b32 (by decide)
  · exact avoids .b33 (by decide)
  · exact avoids .swapScratch (by decide)

private lemma selectArm_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (selectArmStep (model := model) refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · exact swap_frame refs store other avoids
    · rfl

/-- Both possible actual selected arms retain every read outside the row-exchange footprint. -/
lemma select_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (selectStep (model := model) refs store).1.read other = store.read other :=
  selectArm_frame refs (store.read (writeInput refs.lovasz.passes)) store other avoids

/-- Both actual selected arms retain the stored comparison bit exactly. -/
lemma select_passes {model : ExecutionModel} [BitWord.Selected model]
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
  have keyNe := separation.cellKey_ne cell .passes different
  simpa only [writeInput, CInputRef.storageKeys, List.mem_singleton, cellKey] using keyNe

/-- Complete actual second-Lovasz execution retains every read outside its nine possible writes. -/
lemma branchInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs mutableCells other) :
    (branchStep (model := model) refs store).1.read other = store.read other := by
  have comparison : FrameAvoids refs comparisonCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have swap : FrameAvoids refs swapCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  change (selectStep (model := model) refs
    (LatticeLovasz.secondLovaszStore refs.lovasz store)).1.read other = _
  rw [select_frame refs _ other swap, comparison_frame refs _ other comparison]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondLovaszBranch
