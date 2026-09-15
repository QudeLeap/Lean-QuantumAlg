/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix

/-!
# Actual second-pair prefix write footprints

Each phase preserves every actual store read outside its own named writes.
The original transition-wide separation discharges the cross-phase frames.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exactly the named writes of the refresh21 stage. -/
def refresh21Cells : List TransitionCell :=
  [.g21, .refreshG21Product]

/-- Exactly the named writes of the refresh32 stage. -/
def refresh32Cells : List TransitionCell :=
  [.g32, .refreshG32Product]

/-- Exactly the named writes of the inputs stage. -/
def inputsCells : List TransitionCell :=
  [.nu32, .d32, .reductionInputsProduct]

/-- Exactly the named writes of the division stage. -/
def divisionCells : List TransitionCell :=
  [.division32 .magnitude, .division32 .negative, .division32 .wideNumerator,
    .division32 .wideDenominator, .division32 .division, .division32 .output]

/-- Exactly the named writes of the reduction stage. -/
def reductionCells : List TransitionCell :=
  [.reduceProduct, .b31, .b32, .b33]

/-- A read avoids each named cell in a phase's writable footprint. -/
def FrameAvoids (refs : Refs ctx width) (cells : List TransitionCell)
    {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ cell ∈ cells, cellKey refs cell ∉ other.storageKeys

/-- All possible actual writes, across the five chronological prefix stages. -/
def mutableCells : List TransitionCell :=
  refresh21Cells ++ refresh32Cells ++ inputsCells ++ divisionCells ++ reductionCells

/-- The original distinct identities give each named basis read its phase-local frame. -/
theorem basis_avoids (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (cell : LatticeMetricMachine.BasisCell) (cells : List TransitionCell)
    (absent : basisTransitionCell cell ∉ cells) :
    FrameAvoids refs cells (LatticeMetricMachine.basisCellInput refs.basis cell) := by
  intro target member
  have different : target ≠ basisTransitionCell cell := fun equal => absent (equal ▸ member)
  have keyNe := separation.cellKey_ne target (basisTransitionCell cell) different
  cases cell <;>
    simpa only [LatticeMetricMachine.basisCellInput, LatticeState.coordinateInput,
      CInputRef.storageKeys, List.mem_singleton, basisTransitionCell, cellKey] using keyNe

/-- The same original separation gives each retained Gram cell its phase-local frame. -/
theorem metric_avoids (refs : Refs ctx width) (separation : PhaseSeparation refs)
    (cell : LatticeMetricMachine.MetricCell) (cells : List TransitionCell)
    (absent : metricTransitionCell cell ∉ cells) :
    FrameAvoids refs cells
      (writeInput (LatticeMetricMachine.metricCellRef refs.metric cell)) := by
  intro target member
  have different : target ≠ metricTransitionCell cell := fun equal => absent (equal ▸ member)
  have keyNe := separation.cellKey_ne target (metricTransitionCell cell) different
  cases cell <;>
    simpa only [LatticeMetricMachine.metricCellRef, writeInput, CInputRef.storageKeys,
      List.mem_singleton, metricTransitionCell, cellKey] using keyNe

/-- The three named coordinates belonging to a selected original basis row. -/
def rowCells : LatticeMetricMachine.Row → List LatticeMetricMachine.BasisCell
  | .first => [.firstFirst, .firstSecond, .firstThird]
  | .second => [.secondFirst, .secondSecond, .secondThird]
  | .third => [.thirdFirst, .thirdSecond, .thirdThird]

/-- A phase's actual read frame preserves every represented row outside its writes. -/
theorem row_raw_of_frame (refs : Refs ctx width) (separation : PhaseSeparation refs)
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

/-- Any structural writable-cell read avoids a phase whose named cells exclude its identity. -/
theorem write_avoids (refs : Refs ctx width) (separation : PhaseSeparation refs)
    {shape : CShape} (source : CWriteRef ctx shape) (sourceCell : TransitionCell)
    (sourceKey : source.key = cellKey refs sourceCell) (cells : List TransitionCell)
    (absent : sourceCell ∉ cells) : FrameAvoids refs cells (writeInput source) := by
  intro target member
  change cellKey refs target ∉ [source.key]
  rw [sourceKey]
  simp only [List.mem_singleton]
  exact separation.cellKey_ne target sourceCell
    (fun equal => absent (equal ▸ member))

/-- Actual dot refresh preserves all caller reads outside its two written words. -/
theorem refresh21_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs refresh21Cells other) :
    (LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first
      (refreshG21Refs refs) store).read other = store.read other :=
  LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other
    (avoids .g21 (by decide)) (avoids .refreshG21Product (by decide))

/-- Actual dot refresh preserves all caller reads outside its two written words. -/
theorem refresh32_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs refresh32Cells other) :
    (LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
      (refreshG32Refs refs) store).read other = store.read other :=
  LatticeDotRefresh.refreshInto_callerFrame _ _ _ _ other
    (avoids .g32 (by decide)) (avoids .refreshG32Product (by decide))

/-- Actual division-input arithmetic preserves reads outside its three written words. -/
theorem inputs_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs inputsCells other) :
    (LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
      refs.reductionInputs store).read other = store.read other :=
  LatticeSecondReductionInputs.secondReductionInputsInto_callerFrame _ _ _ other
    (avoids .nu32 (by decide)) (avoids .d32 (by decide))
    (avoids .reductionInputsProduct (by decide))

/-- The actual six-cell division footprint is the original transition footprint. -/
theorem division_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs divisionCells other) :
    (RoundedDiv.bodyStep refs.division32 store).1.read other = store.read other := by
  apply RoundedDiv.body_callerFrame refs.division32 store other
  intro key member
  change key ∈ divisionCells.map (cellKey refs) at member
  obtain ⟨cell, cellMember, equal⟩ := List.mem_map.mp member
  rw [← equal]
  exact avoids cell cellMember

/-- Row subtraction preserves all actual reads outside its four written words. -/
theorem reduction_frame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs reductionCells other) :
    (LatticeArithmetic.pointStore (writeInput refs.division32.output)
      refs.basis.second refs.basis.third refs.reduceProduct store).read other =
      store.read other :=
  LatticeArithmetic.pointReduce_callerFrame _ _ _ _ _ other
    (avoids .reduceProduct (by decide)) (avoids .b31 (by decide))
    (avoids .b32 (by decide)) (avoids .b33 (by decide))

/-- Actual prefix execution preserves every read outside the union of its written cells. -/
theorem secondPairPrefixInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : FrameAvoids refs mutableCells other) :
    (secondPairPrefixStep refs store).1.read other = store.read other := by
  have refresh21 : FrameAvoids refs refresh21Cells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have refresh32 : FrameAvoids refs refresh32Cells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have inputs : FrameAvoids refs inputsCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have division : FrameAvoids refs divisionCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  have reduction : FrameAvoids refs reductionCells other := fun cell member =>
    avoids cell (by simp [mutableCells, member])
  change (LatticeArithmetic.pointStore (writeInput refs.division32.output)
    refs.basis.second refs.basis.third refs.reduceProduct
    (RoundedDiv.bodyStep refs.division32 (refreshInputsStep refs store).1).1).read other = _
  rw [reduction_frame refs _ other reduction, division_frame refs _ other division]
  change (LatticeSecondReductionInputs.secondReductionInputsStore (reductionInputs refs)
    refs.reductionInputs (LatticeDotRefresh.refreshStore refs.basis.third refs.basis.second
      (refreshG32Refs refs) (LatticeDotRefresh.refreshStore refs.basis.second refs.basis.first
        (refreshG21Refs refs) store))).read other = _
  rw [inputs_frame refs _ other inputs, refresh32_frame refs _ other refresh32,
    refresh21_frame refs _ other refresh21]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
