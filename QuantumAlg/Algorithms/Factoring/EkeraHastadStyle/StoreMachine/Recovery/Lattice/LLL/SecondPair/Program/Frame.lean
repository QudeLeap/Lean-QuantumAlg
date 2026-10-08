/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Program

/-!
# Complete actual second-pair caller frames

The original global allocation separates every phase's actual writes. Phase
frames compose on chronological stores and retain both coefficient words and
both area words whenever their named cell lies outside a later phase.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Prefix writes embedded in the complete original allocation. -/
def prefixCells : List Cell := LatticeSecondPairMachine.mutableCells.map .transition

/-- Final first-direction writes embedded in the complete original allocation. -/
def postCells : List Cell := LatticeSecondPairPostReduction.mutableCells.map .transition

/-- Seven actual writes of the first squared-area refresh. -/
def area12Cells : List Cell :=
  [.area12ProductLeft, .area12ProductRight, .area12CrossFirst, .area12CrossSecond,
    .area12CrossThird, .area12Result, .area12NormProduct]

/-- Seven actual writes of the second squared-area refresh. -/
def area13Cells : List Cell :=
  [.area13ProductLeft, .area13ProductRight, .area13CrossFirst, .area13CrossSecond,
    .area13CrossThird, .area13Result, .area13NormProduct]

/-- Embed each original second-Lovasz branch identity into the complete allocation. -/
def branchCell : LatticeSecondLovaszBranch.BranchCell → Cell
  | .b11 => .transition .b11
  | .b12 => .transition .b12
  | .b13 => .transition .b13
  | .b21 => .transition .b21
  | .b22 => .transition .b22
  | .b23 => .transition .b23
  | .b31 => .transition .b31
  | .b32 => .transition .b32
  | .b33 => .transition .b33
  | .doubled => .lovaszDoubled
  | .passes => .lovaszPasses
  | .swapScratch => .swapScratch

/-- Nine possible actual writes of the second test and its selected exchange. -/
def branchCells : List Cell := LatticeSecondLovaszBranch.mutableCells.map branchCell

/-- Every actual write after the two direction reductions. -/
def areaBranchCells : List Cell := area12Cells ++ area13Cells ++ branchCells

/-- Every possible actual write of the complete original second-pair transition. -/
def mutableCells : List Cell := prefixCells ++ postCells ++ areaBranchCells

/-- A read avoids the concrete identities of a phase's named mutable cells. -/
def FrameAvoids (refs : Refs ctx width) (cells : List Cell)
    {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ cell ∈ cells, cellKey refs cell ∉ other.storageKeys

/-- The original global identities provide a caller frame for every retained named word or bit. -/
theorem write_avoids (refs : Refs ctx width) (separation : Separation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (sourceCell : Cell)
    (sourceKey : source.key = cellKey refs sourceCell) (cells : List Cell)
    (absent : sourceCell ∉ cells) : FrameAvoids refs cells (LatticeArithmetic.writeInput source)
      := by
  intro target member
  change cellKey refs target ∉ [source.key]
  rw [sourceKey]
  simp only [List.mem_singleton]
  intro equal
  exact absent (separation.keyInjective equal ▸ member)

/-- Original global separation gives each named basis read its phase-local caller frame. -/
theorem basis_avoids (refs : Refs ctx width) (separation : Separation refs)
    (cell : LatticeMetricMachine.BasisCell) (cells : List Cell)
    (absent : .transition (LatticeSecondPairMachine.basisTransitionCell cell) ∉ cells) :
    FrameAvoids refs cells (LatticeMetricMachine.basisCellInput refs.machine.basis cell) := by
  intro target member
  have different : target ≠ .transition (LatticeSecondPairMachine.basisTransitionCell cell) :=
    fun equal => absent (equal ▸ member)
  have keyNe : cellKey refs target ≠
      cellKey refs (.transition (LatticeSecondPairMachine.basisTransitionCell cell)) :=
    fun equal => different (separation.keyInjective equal)
  cases cell <;>
    simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
      CInputRef.storageKeys, List.mem_singleton, LatticeSecondPairMachine.basisTransitionCell,
      cellKey, LatticeSecondPairMachine.cellKey] using keyNe

/-- The actual prefix preserves all reads outside its embedded writable footprint. -/
theorem prefix_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs prefixCells other) :
    (LatticeSecondPairMachine.secondPairPrefixStep (model := model) refs.machine store).1.read
      other =
      store.read other := by
  apply LatticeSecondPairMachine.secondPairPrefixInto_callerFrame refs.machine store other
  intro cell member
  exact avoids (.transition cell) (List.mem_map.mpr ⟨cell, member, rfl⟩)

/-- The actual final direction preserves reads outside its original embedded writes. -/
theorem post_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs postCells other) :
    (LatticeSecondPairPostReduction.postReductionStep (model := model) refs.post store).1.read
      other =
      store.read other := by
  apply LatticeSecondPairPostReduction.postReductionInto_callerFrame refs.post store other
  rw [refs.postMachine]
  intro cell member
  exact avoids (.transition cell) (List.mem_map.mpr ⟨cell, member, rfl⟩)

/-- Actual area-12 refresh preserves every read outside its seven named writes. -/
theorem area12_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs area12Cells other) :
    (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.second
      refs.area12 store).read other = store.read other :=
  LatticeAreaRefresh.refreshInto_callerFrame _ _ _ _ other
    (avoids .area12ProductLeft (by decide))
    (avoids .area12ProductRight (by decide))
    (avoids .area12CrossFirst (by decide))
    (avoids .area12CrossSecond (by decide))
    (avoids .area12CrossThird (by decide))
    (avoids .area12Result (by decide))
    (avoids .area12NormProduct (by decide))

/-- Actual area-13 refresh preserves every read outside its seven named writes. -/
theorem area13_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs area13Cells other) :
    (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.third
      refs.area13 store).read other = store.read other :=
  LatticeAreaRefresh.refreshInto_callerFrame _ _ _ _ other
    (avoids .area13ProductLeft (by decide))
    (avoids .area13ProductRight (by decide))
    (avoids .area13CrossFirst (by decide))
    (avoids .area13CrossSecond (by decide))
    (avoids .area13CrossThird (by decide))
    (avoids .area13Result (by decide))
    (avoids .area13NormProduct (by decide))

/-- Branch references resolve to the same original global cells, including the shared basis. -/
theorem branch_key (refs : Refs ctx width) (cell : LatticeSecondLovaszBranch.BranchCell) :
    LatticeSecondLovaszBranch.cellKey refs.branch cell = cellKey refs (branchCell cell) := by
  cases cell <;> simp only [LatticeSecondLovaszBranch.cellKey, branchCell, cellKey,
    refs.branchBasis, LatticeSecondPairMachine.cellKey]

/-- Actual comparison and selected row exchange preserve reads outside their global footprint. -/
theorem branch_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : FrameAvoids refs branchCells other) :
    (LatticeSecondLovaszBranch.branchStep (model := model) refs.branch store).1.read other =
      store.read other := by
  apply LatticeSecondLovaszBranch.branchInto_callerFrame refs.branch store other
  intro cell member
  rw [branch_key]
  exact avoids (branchCell cell) (List.mem_map.mpr ⟨cell, member, rfl⟩)

/-- Both actual area refreshes and the selected exchange preserve all reads outside their writes. -/
theorem areaBranch_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs areaBranchCells other) :
    (areaBranchStep (model := model) refs store).1.read other = store.read other := by
  have area12 : FrameAvoids refs area12Cells other := fun cell member =>
    avoids cell (by simp [areaBranchCells, member])
  have area13 : FrameAvoids refs area13Cells other := fun cell member =>
    avoids cell (by simp [areaBranchCells, member])
  have branch : FrameAvoids refs branchCells other := fun cell member =>
    avoids cell (by simp [areaBranchCells, member])
  change (LatticeSecondLovaszBranch.branchStep (model := model) refs.branch
    (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.third refs.area13
      (LatticeAreaRefresh.refreshStore refs.machine.basis.first refs.machine.basis.second
        refs.area12 store))).1.read other = _
  rw [branch_frame refs _ other branch, area13_frame refs _ other area13,
    area12_frame refs _ other area12]

/-- All five actual second-pair stages preserve the complete caller frame outside their writes. -/
theorem secondPairInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs mutableCells other) :
    (secondPairStep (model := model) refs store).1.read other = store.read other := by
  have prefixPhase : FrameAvoids refs prefixCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have post : FrameAvoids refs postCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have suffix : FrameAvoids refs areaBranchCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  change (areaBranchStep (model := model) refs
    (LatticeSecondPairPostReduction.postReductionStep (model := model) refs.post
      (LatticeSecondPairMachine.secondPairPrefixStep (model := model)
        refs.machine store).1).1).1.read other = _
  rw [areaBranch_frame refs _ other suffix, post_frame refs _ other post,
    prefix_frame refs _ other prefixPhase]

/-- A phase preserves the complete represented basis when none of its nine cells is written. -/
theorem basis_raw_of_frame (refs : Refs ctx width) (separation : Separation refs)
    {before after : Store ctx} (basis : NumberTheory.IntegerBasis3) (cells : List Cell)
    (rep : LatticeMetricMachine.BasisRawRepresents before refs.machine.basis basis)
    (reads : ∀ {shape : CShape} (other : CInputRef ctx shape),
      FrameAvoids refs cells other → after.read other = before.read other)
    (absent : ∀ cell, .transition (LatticeSecondPairMachine.basisTransitionCell cell) ∉ cells) :
    LatticeMetricMachine.BasisRawRepresents after refs.machine.basis basis := by
  intro row
  cases row with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstFirst))
        basis.first.1
      rw [reads _ (basis_avoids refs separation .firstFirst cells (absent _))]
      exact (rep .first).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstSecond))
        basis.first.2.1
      rw [reads _ (basis_avoids refs separation .firstSecond cells (absent _))]
      exact (rep .first).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .firstThird))
        basis.first.2.2
      rw [reads _ (basis_avoids refs separation .firstThird cells (absent _))]
      exact (rep .first).2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondFirst))
        basis.second.1
      rw [reads _ (basis_avoids refs separation .secondFirst cells (absent _))]
      exact (rep .second).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondSecond))
        basis.second.2.1
      rw [reads _ (basis_avoids refs separation .secondSecond cells (absent _))]
      exact (rep .second).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .secondThird))
        basis.second.2.2
      rw [reads _ (basis_avoids refs separation .secondThird cells (absent _))]
      exact (rep .second).2.2
  | third =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdFirst))
        basis.third.1
      rw [reads _ (basis_avoids refs separation .thirdFirst cells (absent _))]
      exact (rep .third).1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdSecond))
        basis.third.2.1
      rw [reads _ (basis_avoids refs separation .thirdSecond cells (absent _))]
      exact (rep .third).2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.machine.basis .thirdThird))
        basis.third.2.2
      rw [reads _ (basis_avoids refs separation .thirdThird cells (absent _))]
      exact (rep .third).2.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairFullMachine
