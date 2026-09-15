/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FirstPair.Program

/-!
# Actual first-pair write footprints

Each phase preserves every actual store read outside its own named writes.
The original transition-wide separation discharges the cross-phase frames.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exactly the named writes of the division stage. -/
def divisionCells : List TransitionCell :=
  [.magnitude, .negative, .wideNumerator, .wideDenominator, .division, .coefficient]

/-- Exactly the named writes of the reduction stage. -/
def reductionCells : List TransitionCell :=
  [.reduceProduct, .b21, .b22, .b23]

/-- Exactly the named writes of the refresh stage. -/
def refreshCells : List TransitionCell :=
  [.g22, .refreshProduct]

/-- Exactly the named writes of the comparison stage. -/
def comparisonCells : List TransitionCell :=
  [.metricProduct, .passes]

/-- Exactly the named writes of the swap stage. -/
def swapCells : List TransitionCell :=
  [.b11, .b12, .b13, .b21, .b22, .b23, .swapScratch]

/-- A read avoids each named cell in a phase's writable footprint. -/
def FrameAvoids (refs : Refs ctx width) (cells : List TransitionCell)
    {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ cell ∈ cells, cellKey refs cell ∉ other.storageKeys

/-- All possible actual writes, including the optional row-exchange arm. -/
def mutableCells : List TransitionCell :=
  divisionCells ++ reductionCells ++ refreshCells ++ comparisonCells ++ swapCells

/-- The original distinct identities give each named basis read its phase-local frame. -/
theorem basis_avoids (refs : Refs ctx width) (separation : Separation refs)
    (cell : LatticeMetricMachine.BasisCell) (cells : List TransitionCell)
    (absent : basisTransitionCell cell ∉ cells) :
    FrameAvoids refs cells (LatticeMetricMachine.basisCellInput refs.basis cell) := by
  intro target member
  have different : target ≠ basisTransitionCell cell := fun equal => absent (equal ▸ member)
  have keyNe := separation.phase.cellKey_ne target (basisTransitionCell cell) different
  cases cell <;>
    simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
      CInputRef.storageKeys, List.mem_singleton, basisTransitionCell, cellKey] using keyNe

/-- The same original separation gives each retained Gram cell its phase-local frame. -/
theorem metric_avoids (refs : Refs ctx width) (separation : Separation refs)
    (cell : LatticeMetricMachine.MetricCell) (cells : List TransitionCell)
    (absent : metricTransitionCell cell ∉ cells) :
    FrameAvoids refs cells
      (writeInput (LatticeMetricMachine.metricCellRef refs.metric cell)) := by
  intro target member
  have different : target ≠ metricTransitionCell cell := fun equal => absent (equal ▸ member)
  have keyNe := separation.phase.cellKey_ne target (metricTransitionCell cell) different
  cases cell <;>
    simpa only [LatticeMetricMachine.metricCellRef, writeInput, CInputRef.storageKeys,
      List.mem_singleton, metricTransitionCell, cellKey] using keyNe

/-- The three named coordinates belonging to a selected original basis row. -/
def rowCells : LatticeMetricMachine.Row → List LatticeMetricMachine.BasisCell
  | .first => [.firstFirst, .firstSecond, .firstThird]
  | .second => [.secondFirst, .secondSecond, .secondThird]
  | .third => [.thirdFirst, .thirdSecond, .thirdThird]

/-- A phase's actual read frame preserves every represented row outside its writes. -/
theorem row_raw_of_frame (refs : Refs ctx width) (separation : Separation refs)
    {before after : Store ctx} (row : LatticeMetricMachine.Row)
    (value : NumberTheory.IntegerPoint3) (cells : List TransitionCell)
    (rep : LatticeArithmetic.PointRawRepresents before
      (LatticeMetricMachine.rowRefs refs.basis row) value)
    (reads : ∀ {shape : CShape} (other : CInputRef ctx shape),
      FrameAvoids refs cells other → after.read other = before.read other)
    (absent : ∀ cell ∈ rowCells row, basisTransitionCell cell ∉ cells) :
    LatticeArithmetic.PointRawRepresents after (LatticeMetricMachine.rowRefs refs.basis row)
      value := by
  cases row with
  | first =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .firstFirst)) value.1
      rw [reads _ (basis_avoids refs separation .firstFirst cells
        (absent .firstFirst (by decide)))]
      exact rep.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .firstSecond)) value.2.1
      rw [reads _ (basis_avoids refs separation .firstSecond cells
        (absent .firstSecond (by decide)))]
      exact rep.2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .firstThird)) value.2.2
      rw [reads _ (basis_avoids refs separation .firstThird cells
        (absent .firstThird (by decide)))]
      exact rep.2.2
  | second =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .secondFirst)) value.1
      rw [reads _ (basis_avoids refs separation .secondFirst cells
        (absent .secondFirst (by decide)))]
      exact rep.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .secondSecond)) value.2.1
      rw [reads _ (basis_avoids refs separation .secondSecond cells
        (absent .secondSecond (by decide)))]
      exact rep.2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .secondThird)) value.2.2
      rw [reads _ (basis_avoids refs separation .secondThird cells
        (absent .secondThird (by decide)))]
      exact rep.2.2
  | third =>
    refine ⟨?_, ?_, ?_⟩
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .thirdFirst)) value.1
      rw [reads _ (basis_avoids refs separation .thirdFirst cells
        (absent .thirdFirst (by decide)))]
      exact rep.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .thirdSecond)) value.2.1
      rw [reads _ (basis_avoids refs separation .thirdSecond cells
        (absent .thirdSecond (by decide)))]
      exact rep.2.1
    · change RawSignedRepresents
        (after.read (LatticeMetricMachine.basisCellInput refs.basis .thirdThird)) value.2.2
      rw [reads _ (basis_avoids refs separation .thirdThird cells
        (absent .thirdThird (by decide)))]
      exact rep.2.2

/-- The actual six-cell division footprint is the original transition footprint. -/
theorem division_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs divisionCells other) :
    (RoundedDiv.bodyStep refs.division store).1.read other = store.read other := by
  apply RoundedDiv.body_callerFrame refs.division store other
  intro key member
  change key ∈ divisionCells.map (cellKey refs) at member
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact avoids cell cellMember

/-- Row subtraction preserves all actual reads outside its four written words. -/
theorem reduction_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs reductionCells other) :
    (LatticeArithmetic.pointStore (writeInput refs.division.output)
      refs.basis.first refs.basis.second refs.reduceProduct store).read other =
      store.read other :=
  LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other
    (avoids .reduceProduct (by decide)) (avoids .b21 (by decide))
    (avoids .b22 (by decide)) (avoids .b23 (by decide))

/-- Norm refresh preserves all actual reads outside the norm and its product word. -/
theorem refresh_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs refreshCells other) :
    (LatticeNormRefresh.refreshStore refs.basis.second refs.refresh store).read other =
      store.read other := by
  apply LatticeNormRefresh.refreshInto_callerFrame _ _ _ other
  · rw [refs.refreshNorm]
    exact avoids .g22 (by decide)
  · exact avoids .refreshProduct (by decide)

/-- The actual comparison preserves all reads except its product word and decision bit. -/
theorem comparison_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs comparisonCells other) :
    (LatticeLovasz.firstLovaszStore refs.metric refs.lovasz store).read other =
      store.read other :=
  LatticeLovasz.firstLovaszInto_callerFrame _ _ _ other
    (avoids .metricProduct (by decide)) (avoids .passes (by decide))

/-- The actual row exchange preserves all reads outside its six row words and scratch. -/
theorem swap_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (LatticeSwap.pointSwapStore refs.basis.first refs.basis.second refs.swapScratch store).read
      other = store.read other := by
  apply LatticeSwap.pointSwap_callerFrame _ _ _ _ other
  intro cell
  cases cell
  · exact avoids .b11 (by decide)
  · exact avoids .b12 (by decide)
  · exact avoids .b13 (by decide)
  · exact avoids .b21 (by decide)
  · exact avoids .b22 (by decide)
  · exact avoids .b23 (by decide)
  · exact avoids .swapScratch (by decide)

private theorem selectArm_frame (refs : Refs ctx width) (flag : CShape.Value .bit)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (selectArmStep refs flag store).1.read other = store.read other := by
  cases flag with
  | bit flag =>
    cases flag
    · exact swap_frame refs store other avoids
    · rfl

/-- The selected actual arm preserves the full caller frame on both possible outcomes. -/
theorem select_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs swapCells other) :
    (selectStep refs store).1.read other = store.read other :=
  selectArm_frame refs (store.read (writeInput refs.lovasz.passes)) store other avoids

/-- Complete first-pair execution preserves every read outside the union of its actual writes. -/
theorem firstPairInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs mutableCells other) :
    (firstPairStep refs store).1.read other = store.read other := by
  have division : FrameAvoids refs divisionCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have reduction : FrameAvoids refs reductionCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have refresh : FrameAvoids refs refreshCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have comparison : FrameAvoids refs comparisonCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have swap : FrameAvoids refs swapCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  unfold firstPairStep lovaszBranchStep reductionPrefixStep reduceRefreshStep
  rw [select_frame refs _ other swap, comparison_frame refs _ other comparison,
    refresh_frame refs _ other refresh, reduction_frame refs _ other reduction,
    division_frame refs _ other division]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFirstPairMachine
